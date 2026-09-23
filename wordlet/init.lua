-- Wordlet facade: compile a module to a verified C artifact.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local Lex = require("wordlet.lex")
local Parse = require("wordlet.parse")
local Eval = require("wordlet.eval")
local Check = require("wordlet.check")
local C = require("wordlet.cabi")
local Lower = require("wordlet.lower")
local V = require("wordlet.value")

local M = {}

-- options: name, limits
function M.compile(options)
    local options = options or {}
    if type(options.source) ~= "string" then
        D.reject("compile-input", "compile needs a `source` string")
    end
    local name = options.name or "<source>"
    local tokens = Lex.tokens(options.source, name)
    local program = Parse.program(tokens)
    -- A source string has no file to resolve an import against, so only a file may use one.
    for _, decl in ipairs(program.declarations) do
        if decl.kind == "UseDecl" then
            D.reject("import-input",
                "A module that uses another has to be compiled from a file, so that `use "
                .. decl.path .. "` can be resolved next to it", decl.span)
        end
    end
    local session = Eval.new(options)
    local compilation = session:compile(program)
    local functions = {}
    for _, instance in ipairs(session.order) do functions[#functions + 1] = instance.fn end
    Check.program(functions, (compilation.modules and #compilation.modules > 0)
        and compilation.modules or nil, compilation.foreigns)
    local layouts = C.close(compilation)
    -- Emission is computed once here, so the artifact views below only read (lower.close).
    Lower.close(layouts)
    return M.artifact(layouts, compilation)
end

-- Imports -----------------------------------------------------------------------------------------
-- A module is a file. `use util.helper` names `util/helper.let` next to the importing file, and what
-- a module offers is exactly its export list, so nothing else is visible. Each module has its own
-- top-level scope, so a name that is not exported stays private.

local function readModule(path)
    local file, err = io.open(path, "rb")
    if not file then
        D.reject("import-input", "Cannot read " .. path .. ": " .. tostring(err))
    end
    local text = file:read("*a")
    file:close()
    return text
end

local function directoryOf(path)
    return path:match("^(.*)[/\\][^/\\]*$") or "."
end

local function resolveImport(directory, dotted)
    local relative = dotted:gsub("%.", "/")
    if not relative:match("%.let$") then relative = relative .. ".let" end
    return directory .. "/" .. relative
end

-- Loads a module and everything it uses, and returns the module: its namespace, its program and its
-- top scope. `stack` catches a cycle and `cache` loads each file once.
local function loadModule(engine, path, stack, cache)
    local existing = cache[path]
    if existing then return existing end
    for _, open in ipairs(stack) do
        if open == path then
            D.reject("import-cycle", "Module " .. path .. " imports itself through " .. path)
        end
    end
    stack[#stack + 1] = path
    local program = Parse.source(readModule(path), path)
    -- Imports are resolved before the module is loaded, so their namespaces exist before anything is
    -- evaluated.
    local imports = {}
    for _, decl in ipairs(program.declarations) do
        if decl.kind == "UseDecl" then
            imports[#imports + 1] = {
                decl = decl,
                module = loadModule(engine, resolveImport(directoryOf(path), decl.path), stack, cache),
            }
        end
    end
    local saved = engine.top
    local top = engine:load(program)
    for _, item in ipairs(imports) do
        -- The lexical name of an import is the last dotted segment of its path, which is the only
        -- place the AST records it.
        engine:declareNamespace(top, item.decl.path:match("[^.]*$"), item.module.namespace,
            item.decl.span)
    end
    -- A module's initializers run once its imports' namespaces are visible, in declaration order.
    engine:initializeModule(program, top)
    local members = {}
    for _, item in ipairs(program.export.functions) do
        members[item.name.text] = engine:resolveExportItem(item, top)
    end
    for _, item in ipairs(program.export.types) do
        members[item.name.text] = engine:resolveExportItem(item, top)
    end
    local module = { namespace = V.namespace(path, members), program = program, top = top }
    engine.top = saved
    stack[#stack] = nil
    cache[path] = module
    return module
end

-- M.compile_file loads the module graph, then compiles the entry module with its own top scope. A
-- source string with no path cannot resolve an import, so only a file may use one.
function M.compile_file(path, options)
    local engine = Eval.new(options)
    local module = loadModule(engine, path, {}, {})
    engine.top = module.top
    local compilation = engine:compile(module.program, module.top)
    local functions = {}
    for _, instance in ipairs(engine.order) do functions[#functions + 1] = instance.fn end
    Check.program(functions, (compilation.modules and #compilation.modules > 0)
        and compilation.modules or nil, compilation.foreigns)
    local layouts = C.close(compilation)
    Lower.close(layouts)
    return M.artifact(layouts, compilation)
end

function M.artifact(layouts, compilation)
    local artifact = { layouts = layouts, compilation = compilation }
    function artifact:unit() return Lower.unit(self.layouts) end
    -- The type declarations and exported prototypes, for `ffi.cdef` by the JIT loader.
    function artifact:cdef(namespace) return Lower.cdef(self.layouts, namespace) end
    function artifact:source(headerName) return Lower.source(self.layouts, headerName) end
    function artifact:header(name) return Lower.header(self.layouts, name) end
    function artifact:exports()
        local names = {}
        for _, entry in ipairs(self.compilation.functions) do names[#names + 1] = entry.name end
        return names
    end
    return artifact
end

-- Reference interpretation: apply an exported word to concrete arguments and return plain Lua
-- values. This is the differential counterpart of the generated C.
function M.interpret(options)
    local options = options or {}
    local program = Parse.source(options.source, options.name or "<source>")
    local session = Eval.new(options)
    -- The reference interpreter executes the program, so unlike compile-time normalization it may
    -- read and write module storage through the concrete value it names.
    session.run = true
    session:load(program)
    session:initializeModule(program, session.top)
    if type(options.entry) ~= "string" then D.reject("interpret-input", "interpret needs an `entry` name") end
    local word = session:exportedTop(program, options.entry, session.top)
    if V.tag(word) ~= "word" then
        D.reject("function-required", "Entry " .. options.entry .. " is not a word")
    end
    local args = {}
    for index, value in ipairs(options.args or {}) do
        -- A Lua number is a double, so a fractional one is an F64 argument and a whole one is a U32.
        -- An entry that wants an integral F64 takes a U32 and converts it, or a test passes a
        -- fractional value; either way the argument's type is never guessed from the parameter.
        if type(value) == "number" then
            if value % 1 == 0 and value >= 0 and value <= 4294967295 then
                args[index] = V.u32(value)
            else
                args[index] = V.f64(value)
            end
        elseif type(value) == "boolean" then args[index] = V.bool(value)
        elseif type(value) == "string" then args[index] = V.string(S.String, value)
        else D.reject("interpret-arg", "Unsupported argument " .. tostring(value)) end
    end
    local span = word.span
    local result = session:supplyTop(session:staticFrame(session.top, span), word, args, span)
    if V.tag(result) == "word" then
        D.reject("arity", "Entry " .. options.entry .. " needs more arguments to be saturated")
    end
    local out = {}
    for _, value in ipairs(session:expand(result)) do
        -- `describe` is below; it is reached through the module table because a local declared
        -- later is not in scope here.
        out[#out + 1] = M.describe(session, value, {}, 0)
    end
    return out
end

-- Plain description of an interpreted value, so the reference interpreter and the generated C can be
-- compared on aggregates and not only on scalars. A record becomes a field map, a sum alternative
-- becomes its canonical tag index plus its payload, and a reference becomes the target it names.
-- `seen` stops a structure that points back at itself, which a recursive type allows.
local function describe(session, value, seen, depth)
    if depth > 64 then D.resource("interpret-depth", "Interpreted value nests too deeply") end
    local tag = V.tag(value)
    if tag == "string" then return value.bytes end
    if tag == "slice" then
        local items = {}
        for index = 0, value.count - 1 do
            items[index + 1] = describe(session, session:sliceElement(value, index), seen, depth + 1)
        end
        return { slice = true, length = value.count, items = items }
    end
    -- A 64-bit value is held as two words, so it is printed rather than returned as a Lua number.
    -- A float is a Lua number, so it is printed with enough digits to round-trip.
    -- An F64 is a Lua number already, and the differential harness compares it through the C return
    -- type, so the value is handed back as one rather than as a rounded string.
    if tag == "float" then return value.n end
    if tag == "int" and value.high ~= nil then
        return require("wordletkit.u64").tostring(value.high, value.low, value.ty:isSigned())
    end
    if tag == "int" then return value.n end
    if tag == "bool" then return value.b end
    if tag == "unit" then return "unit" end
    if tag == "ref" then
        local object = session:placeObject(value)
        local target = (object and (object.backing or object)) or value.record
        if not target then
            D.todo("interpret-result", "Cannot interpret a reference with no reachable target")
        end
        return { ref = true, target = describe(session, target, seen, depth + 1) }
    end
    if tag == "record" or tag == "object" then
        local backing = value.backing or value
        local fields = backing.fields
        if not fields then
            D.todo("interpret-result", "Cannot interpret a value with no readable fields")
        end
        if seen[value] then return { cycle = true } end
        seen[value] = true
        local out = { record = true }
        for _, field in ipairs(value.ty.fields) do
            out[field.name] = describe(session, fields[field.name], seen, depth + 1)
        end
        seen[value] = nil
        return out
    end
    if tag == "array" then
        local items = value.items
        if not items then
            local backing = value.backing
            items = backing and backing.items or nil
        end
        if not items then
            D.todo("interpret-result", "Cannot interpret an array with no readable elements")
        end
        local out = { array = true }
        for index, item in ipairs(items) do
            out[index] = describe(session, item, seen, depth + 1)
        end
        return out
    end
    if tag == "variant" then
        local index = S.tagIndex(value.ty, value.case)
        if index == nil then D.bug("interpret-result", "A variant has no tag for its alternative") end
        local caseType = S.caseOf(value.ty, value.case)
        return { variant = true, tag = index, case = value.case,
            payload = caseType == S.Unit and "unit"
                or describe(session, value.payload, seen, depth + 1) }
    end
    D.todo("interpret-result", "Cannot interpret result of type " .. S.encode(value.ty or S.Unit))
end

M.describe = describe   -- exported so a test can inspect one value directly
-- The language reference, generated from syntax.md by tools/embed.lua and shipped in the bundle.
M.syntax = require("wordlet.docs.syntax")
-- The design and naming guide, generated from GUIDE.md by tools/embed.lua and shipped in the bundle.
M.guide = require("wordlet.docs.guide")
-- The LuaJIT FFI front end; it requires `ffi` only when something is actually loaded.
M.jit = require("wordlet.jit")

M.session = Eval.new
M.diagnostic = D.format

return M
