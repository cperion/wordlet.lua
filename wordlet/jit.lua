-- A Lua-like front end over the C backend.
--
-- `loadstring` and `loadfile` compile `.let` code to C, build a shared object with the system compiler,
-- and load it with LuaJIT FFI, so the exported words become ordinary Lua-callable functions. `install`
-- registers a searcher, after which `require("a.b")` loads `a/b.let`, and a module's own `use`
-- declarations are resolved next to it by the compiler. On Linux the C source and the object are
-- anonymous memory files (memfd), so nothing is written to disk; elsewhere a temporary directory is
-- used. This is the runtime face of the C backend, not the separate LuaJIT backend.
--
-- `ffi`, the compiler and the ABI layer are required lazily so that loading the compiler never needs
-- them, and so this module can be required while the compiler itself is still being loaded.
local M = {}

-- Where `require` and `M.resolve` look for a `.let` module.
M.path = "./?.let;./?/init.let"

local ffi, W, C, ready

local function prepare()
    if ready then return end
    ffi = require("ffi")
    W = require("wordlet")
    C = require("wordlet.cabi")
    ffi.cdef[[
int memfd_create(const char *name, unsigned int flags);
long write(int fd, const void *buf, unsigned long count);
long lseek(int fd, long offset, int whence);
int close(int fd);
]]
    ready = true
end

local counter = 0
local function namespace()
    counter = counter + 1
    return "wl" .. counter .. "_"
end

local function quote(text) return "'" .. tostring(text):gsub("'", "'\\''") .. "'" end
local function worked(status) return status == true or status == 0 end

local function readFile(path)
    local file = io.open(path, "rb")
    if not file then return nil end
    local text = file:read("*a")
    file:close()
    return text
end

local function writeFile(path, text)
    local file = assert(io.open(path, "wb"), "cannot write " .. path)
    assert(file:write(text))
    assert(file:close())
end

local function remove(path)
    if path then os.remove(path) end
end

-- An anonymous memory file, or nil where the platform has no memfd or a call refuses.
local function memfd(name)
    if os.getenv("WORDLET_NO_MEMFD") then return nil end -- exercise the temporary-directory path
    if not (jit and jit.os == "Linux") then return nil end
    local ok, fd = pcall(ffi.C.memfd_create, name, 0)
    if ok and fd ~= nil and fd >= 0 then return fd end
    return nil
end

local function fill(fd, text)
    local offset, length = 0, #text
    while offset < length do
        local count = ffi.C.write(fd, ffi.cast("const char *", text) + offset, length - offset)
        if not count or count <= 0 then return false end
        offset = offset + count
    end
    return ffi.C.lseek(fd, 0, 0) >= 0
end

-- Compile one translation unit and return the loaded library. `unit` is the C text.
local function build(unit)
    local cc = os.getenv("CC") or "cc"
    local flags = os.getenv("WORDLET_CCFLAGS") or "-O2"
    local inFd = memfd("wordlet.c")
    local outFd = inFd and memfd("wordlet.so")
    local source, object, directory, errors
    if inFd and outFd and fill(inFd, unit) then
        source, object = "/proc/self/fd/" .. inFd, "/proc/self/fd/" .. outFd
        errors = os.tmpname()
    else
        if inFd then ffi.C.close(inFd) end
        if outFd then ffi.C.close(outFd) end
        directory = os.tmpname()
        os.remove(directory)
        if not worked(os.execute("mkdir -p -- " .. quote(directory))) then
            return nil, "cannot create a build directory"
        end
        source, object, errors = directory .. "/module.c", directory .. "/module.so", directory .. "/errors.txt"
        writeFile(source, unit)
    end
    local command = ("%s -std=c11 %s -fPIC -shared -x c %s -o %s 2> %s"):format(
        cc, flags, quote(source), quote(object), quote(errors))
    local status = os.execute(command)
    if not worked(status) then
        local message = readFile(errors) or "the C compiler failed"
        remove(errors)
        if directory then os.execute("rm -rf -- " .. quote(directory)) end
        if inFd then ffi.C.close(inFd) end
        if outFd then ffi.C.close(outFd) end
        return nil, message
    end
    local library = ffi.load(object)
    remove(errors)
    if directory then os.execute("rm -rf -- " .. quote(directory)) end
    -- The input descriptor is no longer needed. The output one is kept open on purpose: dlopen caches
    -- a library by pathname, and `/proc/self/fd/<n>` names a distinct library only while <n> is
    -- unclosed, so closing it would let a later load reuse the path and receive this library.
    if inFd then ffi.C.close(inFd) end
    return library
end

-- Load one compiled artifact: declare its types and exports, build it, and return the module table.
local function publish(artifact, prefix)
    ffi.cdef(artifact:cdef(prefix))
    local library, message = build(artifact:unit())
    if not library then error("wordlet: " .. message, 0) end
    local api = {}
    for _, name in ipairs(artifact:exports()) do
        if name == "init" then
            -- Module storage is assigned by an explicit call, exactly as a C host would do.
            library[prefix .. C.functionName("init")]()
        else
            api[name] = library[prefix .. C.functionName(name)]
        end
    end
    return api
end

-- `loadstring[[...]]`: compile a `.let` string and return its exported words.
function M.loadstring(source, name)
    if type(source) ~= "string" then error("wordlet: loadstring needs a string", 2) end
    prepare()
    local prefix = namespace()
    return publish(W.compile{ source = source, name = name or "<let>", symbolPrefix = prefix }, prefix)
end

-- `loadfile("app.let")`: compile a file; its own `use` imports resolve next to it.
function M.loadfile(path)
    prepare()
    local prefix = namespace()
    return publish(W.compile_file(path, { symbolPrefix = prefix }), prefix)
end

-- Compile and immediately call `main`, returning what it returns.
function M.run(source, name)
    local module = M.loadstring(source, name)
    if module.main == nil then error("wordlet: the program has no `main`", 0) end
    return module.main()
end

-- The path of a `.let` module name under `M.path`, or nil.
function M.resolve(name)
    local relative = name:gsub("%.", "/")
    for pattern in M.path:gmatch("[^;]+") do
        local path = pattern:gsub("%?", relative)
        if readFile(path) then return path end
    end
    return nil
end

local loaded = {}

-- `require` for `.let` modules, cached like `package.loaded`.
function M.require(name)
    if loaded[name] then return loaded[name] end
    local path = M.resolve(name)
    if not path then error("wordlet: no module '" .. tostring(name) .. "' in path", 0) end
    loaded[name] = M.loadfile(path)
    return loaded[name]
end

-- A `package.loaders` entry, so the ordinary `require` finds `.let` modules too.
function M.searcher(name)
    local path = M.resolve(name)
    if not path then return "\n\tno .let module '" .. name .. "'" end
    return function() return M.loadfile(path) end, path
end

function M.install(path)
    if path then M.path = path end
    local searchers = package.loaders or package.searchers
    for _, searcher in ipairs(searchers) do
        if searcher == M.searcher then return M end
    end
    table.insert(searchers, M.searcher)
    return M
end

return M
