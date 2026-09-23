-- C ABI closure: layouts, names and signatures for a verified program.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

-- Encode every non-alphanumeric byte, including underscore, so the mapping is injective.
function M.escape(name)
    return (name:gsub("[^%w]", function(c) return string.format("_%02X", c:byte()) end))
end

function M.functionName(name) return "wordlet_" .. M.escape(name) end

-- A residual instance that no call, view or adapter names is dead. Dropping it before ownership is
-- computed keeps the emitted C free of unreferenced functions, so a private function needs no
-- `inline` keyword to satisfy `-Wunused-function`.
local function liveInstances(compilation)
    local order = compilation.session.order
    local byTarget = {}
    for _, instance in ipairs(order) do byTarget[instance.target] = instance end
    local live, queue = {}, {}
    local function mark(target)
        local instance = byTarget[target]
        if instance and not live[instance] then
            live[instance] = true
            queue[#queue + 1] = instance
        end
    end
    -- Every export and the module initialiser is a root; a callable's code is named by a Call or a
    -- View, and an adapter is generated only for a View that reached emission.
    for _, entry in ipairs(compilation.functions or {}) do mark(entry.instance.target) end
    -- A `Call` or a `View` names the code it reaches; the nested statements of an `If`, a `Switch`
    -- or a `Loop` are visited by `Ir.Stmt:each` on the way.
    local function visit(stmt)
        if stmt.kind == "Call" then mark(stmt.target)
        elseif stmt.kind == "View" then mark(stmt.entry) end
        stmt:each(visit)
    end
    local function walk(list)
        for _, stmt in ipairs(list) do visit(stmt) end
    end
    local index = 1
    while index <= #queue do
        local instance = queue[index]
        index = index + 1
        walk(instance.fn.body)
    end
    local result = {}
    for _, instance in ipairs(order) do if live[instance] then result[#result + 1] = instance end end
    return result
end

function M.close(compilation)
    local order = liveInstances(compilation)
    local layouts = {
        compilation = compilation,
        -- A private function is asked to inline unless the caller opted out; `signatureText` reads it.
        privateInline = not (compilation.session.options and compilation.session.options.inline == false),
        -- Named cells are the identity of a recursive type definition; a reference to one resolves
        -- to the definition's layout, which must be named so its forward declaration is emitted.
        typeCells = (compilation.session and compilation.session.typeCells) or {},
        tuples = {},        -- result vector -> { name, fields }
        tupleOrder = {},
        views = {},         -- Ty.View -> invocation-pointer layout
        viewOrder = {},
        records = {},       -- Ty.Record -> { name, fields }
        recordOrder = {},
        arrays = {},        -- Ty.Array -> { name, element, length }
        arrayOrder = {},
        slices = {},        -- Ty.Slice -> { name, element }
        sliceOrder = {},
        strings = {},      -- distinct string literals, in first-use order
        stringIndex = {},
        stringCount = 0,
        sums = {},          -- Ty.Sum -> { name, cases }
        sumOrder = {},
        tagged = {},        -- Ty.Tagged -> { name, cases }
        taggedOrder = {},
        signatures = {},
    }

    local function recordLayout(ty0)
        local ty = S.environmentOf(ty0)
        local existing = layouts.records[ty]
        if existing then return existing end
        local layout = { name = "wordletrecord_" .. (#layouts.recordOrder + 1), type = ty, fields = {} }
        layouts.records[ty] = layout
        layouts.recordOrder[#layouts.recordOrder + 1] = layout
        for _, field in ipairs(ty.fields) do
            layout.fields[#layout.fields + 1] = { name = "f_" .. M.escape(field.name), type = field.type }
            -- Name nested field types too, so their declarations precede this struct.
            if S.runtime(field.type) and field.type ~= S.Unit then
                layouts:cType(field.type)
            end
        end
        return layout
    end


    -- An array is a struct holding one C array, because a bare C array cannot be copied or
    -- returned by value while a struct that contains one can.
    local function arrayLayout(ty)
        local existing = layouts.arrays[ty]
        if existing then return existing end
        local layout = { name = "wordletarray_" .. (#layouts.arrayOrder + 1), type = ty,
            element = ty.element, length = ty.length }
        layouts.arrays[ty] = layout
        layouts.arrayOrder[#layouts.arrayOrder + 1] = layout
        -- The element is embedded by value, so its layout must exist and be complete.
        layouts:cType(ty.element)
        return layout
    end

    -- A slice is a pointer and a length. The pointer member is what keeps a slice finite even when
    -- its element type is recursive: the element's layout is named, but a pointer to an incomplete
    -- type is a complete type, so `Slice(Node)` inside `Node` is a legal layout.
    local function sliceLayout(ty)
        local existing = layouts.slices[ty]
        if existing then return existing end
        local layout = { name = "wordletslice_" .. (#layouts.sliceOrder + 1), type = ty,
            element = ty.element }
        layouts.slices[ty] = layout
        layouts.sliceOrder[#layouts.sliceOrder + 1] = layout
        layouts:cType(ty.element)
        return layout
    end
    layouts.sliceLayout = sliceLayout

    -- A sum and a tagged callable are both a tag plus a union of alternative payloads, so they share
    -- one layout: only the struct name and the table that owns it differ. Payloads are held by value
    -- so construction and projection are plain assignments.
    local function tagLayout(prefix, table_, order, ty)
        local existing = table_[ty]
        if existing then return existing end
        local layout = { name = prefix .. (#order + 1), type = ty, cases = {} }
        table_[ty] = layout
        order[#order + 1] = layout
        for index, field in ipairs(S.alternatives(ty)) do
            layout.cases[#layout.cases + 1] = { name = "f_" .. M.escape(field.name), type = field.type,
                tag = index - 1 }
            if field.type ~= S.Unit and S.runtime(field.type) then layouts:cType(field.type) end
        end
        return layout
    end

    local function sumLayout(ty) return tagLayout("wordletsum_", layouts.sums, layouts.sumOrder, ty) end
    local function taggedLayout(ty)
        return tagLayout("wordlettag_", layouts.tagged, layouts.taggedOrder, ty)
    end

    local function resultLayout(results)
        if #results == 0 then return { kind = "void" } end
        if #results == 1 then
            if results[1] == S.Unit then return { kind = "void", unit = true } end
            return { kind = "scalar", type = results[1] }
        end
        local key = S.encode(S.list(results))
        local existing = layouts.tuples[key]
        if existing then return existing end
        local layout = { kind = "tuple", name = "wordlettuple_" .. (#layouts.tupleOrder + 1), fields = {} }
        layouts.tuples[key] = layout
        layouts.tupleOrder[#layouts.tupleOrder + 1] = layout
        for index, ty in ipairs(results) do
            layout.fields[#layout.fields + 1] = { name = "f_" .. index, type = ty }
        end
        return layout
    end

    -- One C struct per distinct visible signature: an invocation pointer and an environment.
    -- An owned callable with an empty environment is pure code, and its C representation is the
    -- same invocation pointer plus a null environment as any other view.
    local function viewLayout(ty0)
        -- A view and an owned callable both carry the signature a view is built from.
        local ty = S.view(ty0.visible)
        local existing = layouts.views[ty]
        if existing then return existing end
        local sig = ty.visible
        local parameters = { "const void *environment" }
        for index, input in ipairs(sig.inputs) do
            if input.kind ~= "InValue" then
                D.todo("view-input", "Only by-value callable inputs have a C representation yet")
            end
            parameters[#parameters + 1] = layouts:cType(input.type) .. " a" .. index
        end
        local results = resultLayout(sig.results)
        local returns = results.kind == "void" and "void"
            or (results.kind == "scalar" and layouts:cType(results.type) or results.name)
        local types = { "const void *" }
        for _, input in ipairs(sig.inputs) do types[#types + 1] = layouts:cType(input.type) end
        local layout = {
            name = "wordletview_" .. (#layouts.viewOrder + 1),
            type = ty, parameters = parameters, results = results, returns = returns,
            arguments = #sig.inputs,
            invoke = "(" .. table.concat(types, ", ") .. ")",
        }
        layouts.views[ty] = layout
        layouts.viewOrder[#layouts.viewOrder + 1] = layout
        return layout
    end

    -- An adapter binds a callable's hidden inputs so it can be invoked through a view. Its struct
    -- holds the bound values (or borrowed pointers) and its function forwards the visible inputs.
    layouts.adapterIndex, layouts.adapterOrder = {}, {}
    function layouts:viewAdapter(entry, bound)
        local key = entry .. "|" .. #bound
        for _, slot in ipairs(bound) do key = key .. "|" .. S.encode(slot.type) .. (slot.pointer and "*" or "") end
        local existing = self.adapterIndex[key]
        if existing then return existing end
        local index = #self.adapterOrder + 1
        local fields = {}
        for position, slot in ipairs(bound) do
            fields[position] = { name = "f_" .. position, type = slot.type, pointer = slot.pointer }
        end
        local adapter = { name = "wordletadapterstruct_" .. index, fn = "wordletadapterfn_" .. index,
            entry = entry, bound = fields, struct = "wordletadapterstruct_" .. index }
        self.adapterIndex[key] = adapter
        self.adapterOrder[#self.adapterOrder + 1] = adapter
        return adapter
    end

    layouts.recordLayout, layouts.resultLayout, layouts.viewLayout = recordLayout, resultLayout, viewLayout
    -- Either tagged family, which is what the variant statements name.
    layouts.arrayLayout = arrayLayout
    layouts.sumLayout = sumLayout
    layouts.taggedLayout = taggedLayout
    function layouts.tagLayout(ty) return S.isTagged(ty) and taggedLayout(ty) or sumLayout(ty) end

    function layouts:resolveNamed(ty)
        local cell = layouts.typeCells[ty.cell]
        if not cell then
            D.bug("c-named", "A named type cell has no definition: " .. tostring(ty.cell))
        end
        return cell
    end

    function layouts:cType(ty)
        if S.isNamed(ty) then return layouts:cType(layouts:resolveNamed(ty)) end
        if S.isPtr(ty) then
            -- Same C type as a reference, and deliberately a different language type.
            return layouts:cType(ty.target) .. " *"
        end
        if S.isRef(ty) then
            -- A pointer to a target, so the target needs a declaration but not a definition here.
            return layouts:cType(ty.target) .. " *"
        end
        if ty == S.F64 then
            -- The host's own double, so the arithmetic below the boundary is IEEE-754 exactly.
            layouts.usesFloat = true
            return "double"
        end
        if ty == S.U32 then return "uint32_t" end
        if ty == S.U8 then return "uint8_t" end
        if ty == S.U16 then return "uint16_t" end
        if ty == S.U64 then
            layouts.usesWide = true
            return "uint64_t"
        end
        if ty == S.I64 then
            layouts.usesWide = true
            layouts.usesSigned64 = true
            return "int64_t"
        end
        if ty == S.I32 then
            -- The unit needs the signed helpers, which reinterpret rather than rely on the
            -- implementation's conversion of an out-of-range value.
            layouts.usesSigned = true
            return "int32_t"
        end
        if ty == S.Bool then
            layouts.usesBool = true
            return "bool"
        end
        if ty == S.Unit then return "void" end
        if S.isView(ty) then return viewLayout(ty).name end
        if S.isOwned(ty) and S.environmentOf(ty) ~= S.Unit then return layouts:cType(ty.environment) end
        if S.isOwned(ty) then return viewLayout(ty).name end
        if S.isRecord(ty) then return recordLayout(ty).name end
        if S.isArray(ty) then return arrayLayout(ty).name end
        if S.isSlice(ty) then return sliceLayout(ty).name end
        if S.isSum(ty) then return sumLayout(ty).name end
        if S.isTagged(ty) then return taggedLayout(ty).name end
        D.todo("c-type", "No C representation for " .. S.encode(ty))
    end

    -- Public names: the first export of an instance uses the export name; extra aliases become
    -- forwarding wrappers emitted by the backend.
    -- A `symbolPrefix` namespaces every exported symbol, so several artifacts can be loaded side by
    -- side in one process (the JIT loader uses it); the default keeps the documented `wordlet_` names.
    local prefix = (compilation.session.options and compilation.session.options.symbolPrefix) or ""
    local exported = {}
    for _, entry in ipairs(compilation.functions) do
        local instance = entry.instance
        local name = prefix .. M.functionName(entry.name)
        if exported[instance.target] then
            exported[instance.target].aliases[#exported[instance.target].aliases + 1] = name
        else
            exported[instance.target] = { name = name, instance = instance, aliases = {} }
        end
    end

    local signatures = {}
    local function signature(fn, cName, hidden)
        local params, placeParams = {}, {}
        for _, param in ipairs(fn.params) do
            if param.kind == "ValueParam" then
                -- The C parameter is named after the SSA value so Ref() lowers directly, and the
                -- binding it names is recorded so the emitter can ask the IR whether the body uses it.
                params[#params + 1] = { name = "v" .. param.binding.id, type = param.type,
                    input = param.input, binding = param.binding.id }
            elseif param.kind == "PlaceParam" then
                -- A borrowed receiver is a pointer; its storage id names the pointed-to object.
                params[#params + 1] = { name = "s" .. param.binding.id, type = param.type,
                    input = param.input, pointer = true, binding = param.binding.id }
                placeParams[param.binding.id] = true
            else
                D.todo("c-input", "Only by-value and borrowed inputs have a C representation yet")
            end
        end
        return { fn = fn, name = cName, params = params, placeParams = placeParams,
            results = resultLayout(fn.results), hidden = hidden or 0 }
    end

    for _, instance in ipairs(order) do
        local entry = exported[instance.target]
        local cName = entry and entry.name or instance.target
        signatures[instance.target] = signature(instance.fn, cName)
        signatures[instance.target].aliases = entry and entry.aliases or {}
        signatures[instance.target].exported = entry ~= nil
    end

    -- A foreign declaration has no instance to specialize and no body to emit, so its signature is its
    -- declared shape and its name is the host symbol. The prototype is what the call site needs.
    layouts.foreignOrder = {}
    for _, foreign in ipairs(compilation.foreigns or {}) do
        local params = {}
        for index, ty in ipairs(foreign.inputTypes) do
            params[#params + 1] = { name = "a" .. index, type = ty, input = index - 1 }
        end
        local entry = { fn = { id = foreign.target, params = {}, results = foreign.results },
            name = foreign.target, params = params, placeParams = {}, foreign = true,
            results = resultLayout(foreign.results), hidden = 0 }
        signatures[foreign.target] = entry
        layouts.foreignOrder[#layouts.foreignOrder + 1] = entry
    end

    -- Exported record types get a public alias so consumers never name a numbered struct.
    layouts.typeExports = {}
    for _, entry in ipairs(compilation.types or {}) do
        -- A sum is nameable too; only the numbered layout name differs.
        local layout = S.isSum(entry.type) and sumLayout(entry.type) or recordLayout(entry.type)
        layouts.typeExports[#layouts.typeExports + 1] = {
            name = "wordtype_" .. M.escape(entry.name), layout = layout, entry = entry,
        }
    end
    -- An adapter function's return type must be named before the adapter body is printed.
    for _, instance in ipairs(order) do
        local signature = signatures[instance.target]
        if signature and signature.results.kind == "scalar" and S.runtime(signature.results.type) then
            layouts:cType(signature.results.type)
        end
    end
    -- Name every runtime type before emission, so aggregate declarations precede their uses.
    -- A parameter's type is named by `signature`, but a result type is not.
    for _, instance in ipairs(order) do
        local signature = signatures[instance.target]
        for _, param in ipairs(signature.params) do
            if S.runtime(param.type) then layouts:cType(param.type) end
        end
        if signature.results.kind == "scalar" and S.runtime(signature.results.type) then
            layouts:cType(signature.results.type)
        end
    end
    -- Sum layouts are reached through cType, which may run while the statements are emitted.
    layouts.signatures = signatures
    -- Module-level storages are file-scope objects; the emitter names them here.
    layouts.modules = {}
    layouts.moduleOrder = {}
    for index, module in ipairs(compilation.modules or {}) do
        local entry = { name = "wordletmodule_" .. index, storage = module.storage,
            type = module.type, source = module.name }
        layouts.modules[module.storage] = entry
        layouts.moduleOrder[#layouts.moduleOrder + 1] = entry
    end
    layouts.order = order
    layouts.symbolPrefix = prefix
    return layouts
end

return M
