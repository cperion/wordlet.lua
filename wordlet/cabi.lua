-- C ABI closure: layouts, names and signatures for a verified program.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

-- Encode every non-alphanumeric byte, including underscore, so the mapping is injective.
function M.escape(name)
    return (name:gsub("[^%w]", function(c) return string.format("_%02X", c:byte()) end))
end

function M.functionName(name) return "wordlet_" .. M.escape(name) end

-- One registry per layout family: the layouts of one kind, in the order they were created, keyed by
-- the type that asked for them. A registry owns both, so a layout and its place in the emitted
-- declarations cannot drift.
local function registry(prefix) return { prefix = prefix, index = {}, order = {} } end

-- The C name of the `index`th layout of a family.
local function layoutName(prefix, index) return prefix .. index end

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
        typeCells = (compilation.session and compilation.session.types.cells) or {},
        records = registry("wordletrecord_"),
        arrays = registry("wordletarray_"),
        slices = registry("wordletslice_"),
        sums = registry("wordletsum_"),
        tagged = registry("wordlettag_"),
        tuples = registry("wordlettuple_"),
        views = registry("wordletview_"),
        adapters = registry("wordletadapterstruct_"),
        modules = registry("wordletmodule_"),
        strings = {},      -- distinct string literals, in first-use order
        stringIndex = {},
        stringCount = 0,
        signatures = {},
    }

    local function recordLayout(ty0)
        local ty = S.environmentOf(ty0)
        local existing = layouts.records.index[ty]
        if existing then return existing end
        local layout = { name = layoutName(layouts.records.prefix, #layouts.records.order + 1),
            type = ty, fields = {} }
        layouts.records.index[ty] = layout
        layouts.records.order[#layouts.records.order + 1] = layout
        for _, field in ipairs(ty.fields) do
            layout.fields[#layout.fields + 1] = { name = "f_" .. M.escape(field.name), type = field.type }
            -- Name nested field types too, so their declarations precede this struct.
            if S.runtime(field.type) and field.type ~= S.unit then
                layouts:cType(field.type)
            end
        end
        return layout
    end


    -- An array is a struct holding one C array, because a bare C array cannot be copied or
    -- returned by value while a struct that contains one can.
    local function arrayLayout(ty)
        local existing = layouts.arrays.index[ty]
        if existing then return existing end
        local layout = { name = layoutName(layouts.arrays.prefix, #layouts.arrays.order + 1), type = ty,
            element = ty.element, length = ty.length }
        layouts.arrays.index[ty] = layout
        layouts.arrays.order[#layouts.arrays.order + 1] = layout
        -- The element is embedded by value, so its layout must exist and be complete.
        layouts:cType(ty.element)
        return layout
    end

    -- A slice is a pointer and a length. The pointer member is what keeps a slice finite even when
    -- its element type is recursive: the element's layout is named, but a pointer to an incomplete
    -- type is a complete type, so `slice(node)` inside `node` is a legal layout.
    local function sliceLayout(ty)
        local existing = layouts.slices.index[ty]
        if existing then return existing end
        local layout = { name = layoutName(layouts.slices.prefix, #layouts.slices.order + 1), type = ty,
            element = ty.element }
        layouts.slices.index[ty] = layout
        layouts.slices.order[#layouts.slices.order + 1] = layout
        layouts:cType(ty.element)
        return layout
    end
    layouts.sliceLayout = sliceLayout

    -- A sum and a tagged callable are both a tag plus a union of alternative payloads, so they share
    -- one layout: only the struct name and the table that owns it differ. Payloads are held by value
    -- so construction and projection are plain assignments.
    local function tagLayout(family, ty)
        local existing = family.index[ty]
        if existing then return existing end
        local layout = { name = layoutName(family.prefix, #family.order + 1), type = ty, cases = {} }
        family.index[ty] = layout
        family.order[#family.order + 1] = layout
        for index, field in ipairs(S.alternatives(ty)) do
            layout.cases[#layout.cases + 1] = { name = "f_" .. M.escape(field.name), type = field.type,
                tag = index - 1 }
            if field.type ~= S.unit and S.runtime(field.type) then layouts:cType(field.type) end
        end
        return layout
    end

    local function sumLayout(ty) return tagLayout(layouts.sums, ty) end
    local function taggedLayout(ty) return tagLayout(layouts.tagged, ty) end

    local function resultLayout(results)
        if #results == 0 then return { kind = "void" } end
        if #results == 1 then
            if results[1] == S.unit then return { kind = "void", unit = true } end
            return { kind = "scalar", type = results[1] }
        end
        local key = S.encode(S.list(results))
        local existing = layouts.tuples.index[key]
        if existing then return existing end
        local layout = { kind = "tuple", name = layoutName(layouts.tuples.prefix, #layouts.tuples.order + 1),
            fields = {} }
        layouts.tuples.index[key] = layout
        layouts.tuples.order[#layouts.tuples.order + 1] = layout
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
        local existing = layouts.views.index[ty]
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
            name = layoutName(layouts.views.prefix, #layouts.views.order + 1),
            type = ty, parameters = parameters, results = results, returns = returns,
            arguments = #sig.inputs,
            invoke = "(" .. table.concat(types, ", ") .. ")",
        }
        layouts.views.index[ty] = layout
        layouts.views.order[#layouts.views.order + 1] = layout
        return layout
    end

    -- An adapter binds a callable's hidden inputs so it can be invoked through a view. Its struct
    -- holds the bound values (or borrowed pointers) and its function forwards the visible inputs.
    -- The adapter family is a registry like the others, so its key list and its order list live in one
    function layouts:viewAdapter(entry, bound)
        local key = entry .. "|" .. #bound
        for _, slot in ipairs(bound) do key = key .. "|" .. S.encode(slot.type) .. (slot.pointer and "*" or "") end
        local existing = self.adapters.index[key]
        if existing then return existing end
        local index = #self.adapters.order + 1
        local fields = {}
        for position, slot in ipairs(bound) do
            fields[position] = { name = "f_" .. position, type = slot.type, pointer = slot.pointer }
        end
        local adapter = { name = layoutName(layouts.adapters.prefix, index),
            fn = layoutName("wordletadapterfn_", index),
            entry = entry, bound = fields, struct = layoutName(layouts.adapters.prefix, index) }
        self.adapters.index[key] = adapter
        self.adapters.order[#self.adapters.order + 1] = adapter
        return adapter
    end

    layouts.recordLayout, layouts.resultLayout, layouts.viewLayout = recordLayout, resultLayout, viewLayout
    -- Either tagged family, which is what the variant statements name.
    layouts.arrayLayout = arrayLayout
    layouts.sumLayout = sumLayout
    layouts.taggedLayout = taggedLayout
    function layouts.tagLayout(ty) return ty:isTagged() and taggedLayout(ty) or sumLayout(ty) end

    function layouts:resolveNamed(ty)
        local cell = layouts.typeCells[ty.cell]
        if not cell then
            D.bug("c-named", "A named type cell has no definition: " .. tostring(ty.cell))
        end
        return cell
    end

    function layouts:cType(ty)
        if ty:isNamed() then return layouts:cType(layouts:resolveNamed(ty)) end
        if ty:isPtr() then
            -- Same C type as a reference, and deliberately a different language type.
            return layouts:cType(ty.target) .. " *"
        end
        if ty:isRef() then
            -- A pointer to a target, so the target needs a declaration but not a definition here.
            return layouts:cType(ty.target) .. " *"
        end
        if ty == S.f64 then
            -- The host's own double, so the arithmetic below the boundary is IEEE-754 exactly.
            layouts.usesFloat = true
            return "double"
        end
        if ty == S.u32 then return "uint32_t" end
        if ty == S.u8 then return "uint8_t" end
        if ty == S.u16 then return "uint16_t" end
        if ty == S.u64 then
            layouts.usesWide = true
            return "uint64_t"
        end
        if ty == S.i64 then
            layouts.usesWide = true
            layouts.usesSigned64 = true
            return "int64_t"
        end
        if ty == S.i32 then
            -- The unit needs the signed helpers, which reinterpret rather than rely on the
            -- implementation's conversion of an out-of-range value.
            layouts.usesSigned = true
            return "int32_t"
        end
        if ty == S.bool then
            layouts.usesBool = true
            return "bool"
        end
        if ty == S.unit then return "void" end
        if ty:isView() then return viewLayout(ty).name end
        if ty:isOwned() and S.environmentOf(ty) ~= S.unit then return layouts:cType(ty.environment) end
        if ty:isOwned() then return viewLayout(ty).name end
        if ty:isRecord() then return recordLayout(ty).name end
        if ty:isArray() then return arrayLayout(ty).name end
        if ty:isSlice() then return sliceLayout(ty).name end
        if ty:isSum() then return sumLayout(ty).name end
        if ty:isTagged() then return taggedLayout(ty).name end
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
    local function signature(fn, cName)
        local params, placeParams = {}, {}
        for _, param in ipairs(fn.params) do
            if param.kind == "ValueParam" then
                -- The C parameter is named after the SSA value so ref() lowers directly, and the
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
            results = resultLayout(fn.results) }
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
        local layout = entry.type:isSum() and sumLayout(entry.type) or recordLayout(entry.type)
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
    for index, module in ipairs(compilation.modules or {}) do
        local entry = { name = layoutName(layouts.modules.prefix, index), storage = module.storage,
            type = module.type, source = module.name }
        layouts.modules.index[module.storage] = entry
        layouts.modules.order[#layouts.modules.order + 1] = entry
    end
    layouts.order = order
    layouts.symbolPrefix = prefix
    return layouts
end

return M
