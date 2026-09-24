-- Contextual C body emission. The instruction renderer remains in lower.lua; this module owns
-- static destinations, tail groups, optional expansion credit and discovery of real C roots.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local Tail = require("wordlet.tail")
local Analysis = require("wordlet.analysis")
local M = {}

local function option(value, default, name)
    if value == nil then return default end
    if type(value) ~= "number" or value < 0 or value == math.huge or value % 1 ~= 0 then
        D.reject("compile-option", name .. " must be a finite nonnegative integer")
    end
    return value
end
local function fresh(unit)
    unit.nextName = unit.nextName + 1
    return "wlctx" .. unit.nextName .. "_"
end
local function paramName(emitter, param)
    if param.pointer then return emitter:storage(param.binding) end
    return emitter:value(param.binding)
end
local function arguments(emitter, call)
    local out = {}
    for _, arg in ipairs(call.arguments) do
        if arg.kind == "ValueArg" then out[#out + 1] = emitter:expr(arg.value)
        elseif arg.kind == "BorrowArg" then out[#out + 1] = emitter:borrow(arg.place)
        else D.bug("c-arg", "Unknown contextual argument " .. tostring(arg.kind)) end
    end
    return out
end

-- nil means the existing ordinary ABI call emitter should handle the call. A numeric answer is
-- the number of source statements consumed, including the exact Return paired with a tail call.
function M.call(emitter, call, list, index)
    local unit = emitter.unit
    local plan = unit.plan
    local signature = emitter.layouts.signatures[call.target]
    if not signature then D.bug("c-target", "Call to unknown function " .. call.target) end
    local component = plan.componentOf[call.target]
    local site = plan.tailSites[call]
    if site and (site.list ~= list or site.index ~= index or site.returned ~= list[index + 1]) then
        D.bug("tail-site", "Tail evidence does not match the emitted call occurrence")
    end
    local target = site and emitter.group.entries[call.target]
    if target then
        if not emitter.group.component.cyclic then D.bug("tail-component", "Acyclic group has an internal tail edge") end
        local values, saved = arguments(emitter, call), {}
        -- Snapshot ALL RHS values before writing any carrier, including unchanged/swapped inputs.
        for i, param in ipairs(signature.params) do
            local name = emitter:tempName()
            emitter:line(emitter.layouts:cType(param.type) .. (param.pointer and " *" or " ") .. name .. " = " .. values[i] .. ";")
            saved[i] = name
        end
        for i, param in ipairs(signature.params) do emitter:line(paramName(target, param) .. " = " .. saved[i] .. ";") end
        emitter:line("goto " .. target.entryLabel .. ";")
        unit.jumps = unit.jumps + 1
        return 2
    end
    if component and not unit.active[component.id] and unit.depth < 32 and component.cost <= unit.remaining then
        unit.remaining = unit.remaining - component.cost
        local values = arguments(emitter, call)
        local destination
        if site then
            destination = emitter.destination
        else
            destination = {types = signature.fn.results, outputs = {}, label = fresh(unit) .. "resume"}
            for i, value in ipairs(call.results) do
                if emitter.usedValues[value.id] then
                    destination.outputs[i] = emitter:value(value.id)
                    emitter:declare(destination.types[i], destination.outputs[i])
                end
            end
        end
        emitter:line("{")
        M.group(emitter.layouts, unit, component, call.target, values, destination,
            emitter.lines, emitter.indent + 1, not site, false)
        emitter:line("}")
        if not site and destination.used then emitter:line(destination.label .. ": ;") end
        unit.expansions = unit.expansions + 1
        return site and 2 or 1
    end
    if component then
        local reason = unit.active[component.id] and "recursive-context"
            or (unit.depth >= 32 and "expansion-depth" or "expansion-budget")
        unit.requireRoot(call.target)
        unit.edges[#unit.edges + 1] = call.target
        unit.callReasons[#unit.callReasons + 1] = {target = call.target, reason = reason}
    end
    unit.calls = unit.calls + 1
end

-- A CExit uses the ordinary return renderer. A local destination is compiler state, not a selector
-- stored in C. Snapshot the entire used result vector before installing the caller's bindings.
function M.returnText(emitter, values)
    local destination = emitter.destination
    if destination.exit then return nil end
    if #values ~= #destination.types then D.bug("c-return", "Local return interface mismatch") end
    local statements, saved = {}, {}
    for i, value in ipairs(values) do
        if value.type ~= destination.types[i] then D.bug("c-return", "Local return type mismatch") end
        if destination.outputs[i] then
            local name = emitter:tempName()
            statements[#statements + 1] = emitter.layouts:cType(value.type) .. " " .. name .. " = " .. emitter:expr(value) .. ";"
            saved[i] = name
        else
            -- The template analysis includes this return use. Preserve it for discarded results
            -- too, rather than leaving call/shared/View definitions unused in the copied body.
            statements[#statements + 1] = "(void)(" .. emitter:expr(value) .. ");"
        end
    end
    for i = 1, #values do
        if destination.outputs[i] then statements[#statements + 1] = destination.outputs[i] .. " = " .. saved[i] .. ";" end
    end
    if values ~= emitter.fallthroughValues then
        destination.used = true
        statements[#statements + 1] = "goto " .. destination.label .. ";"
    end
    return "{ " .. table.concat(statements, " ") .. " }"
end

function M.group(layouts, unit, component, selected, args, destination, lines, indent, fallsIntoDestination, root)
    if unit.active[component.id] then D.bug("tail-active", "Expanded an overlapping activation") end
    local total = unit.account.weight + component.cost
    if total > unit.account.limit then D.resource("c-size", "Contextual C emission exceeds its emitted-node budget") end
    unit.account.weight, unit.weight = total, unit.weight + component.cost
    local group = {component = component, destination = destination, entries = {}}
    local header = unit.newEmitter(layouts, nil, {storageUses={}, valueUses={}, paramValues={}})
    header.lines, header.indent = lines, indent
    -- Complete reservation precedes any member body: mutual edges can always find their labels.
    for _, id in ipairs(component.entries) do
        local signature = layouts.signatures[id]
        local analysis = unit.analyses[id]
        if not analysis then analysis = Analysis.analyze(unit.plan.functions[id]); unit.analyses[id] = analysis end
        local emitter = unit.newEmitter(layouts, signature, analysis)
        emitter.prefix = (root and id == selected) and "" or fresh(unit)
        emitter.lines, emitter.indent = lines, indent + (component.cyclic and 1 or 0)
        emitter.unit, emitter.group, emitter.destination = unit, group, destination
        emitter.entryLabel = emitter.prefix .. "wl_entry"
        group.entries[id] = emitter
        if not (root and id == selected) then
            for i, param in ipairs(signature.params) do
                local declaration = layouts:cType(param.type) .. (param.pointer and " *" or " ") .. paramName(emitter, param)
                if id == selected then declaration = declaration .. " = " .. args[i] end
                header:line(declaration .. ";")
            end
        end
        local body = unit.plan.functions[id].body
        local last = body[#body]
        if fallsIntoDestination and not component.cyclic and last and last.kind == "Return" then
            emitter.fallthroughValues = last.values
        end
    end
    if component.cyclic then header:line("goto " .. group.entries[selected].entryLabel .. ";") end
    unit.active[component.id], unit.depth = true, unit.depth + 1
    for _, id in ipairs(component.entries) do
        local emitter, signature = group.entries[id], layouts.signatures[id]
        if component.cyclic then header:line(emitter.entryLabel .. ": {") end
        emitter:statements(unit.plan.functions[id].body)
        for _, param in ipairs(signature.params) do
            local used
            if param.pointer then used = emitter.usedStorages[param.binding]
            else used = emitter.usedValues[param.binding] end
            if not used then emitter:line("(void)" .. paramName(emitter, param) .. ";") end
        end
        if component.cyclic then header:line("}") end
    end
    unit.active[component.id], unit.depth = nil, unit.depth - 1
end

-- Returns buffered bodies without C signatures. The caller renders signatures after this function
-- has closed the actual root graph and computed recursive linkage eligibility.
function M.bodies(layouts, newEmitter)
    local options = layouts.compilation.session.options or {}
    local budget = option(options.residualInlineBudget, 0, "residualInlineBudget")
    local limit = option(options.limits and options.limits.emittedNodes, 1000000, "limits.emittedNodes")
    local functions, byTarget = {}, {}
    for _, instance in ipairs(layouts.order) do
        functions[#functions + 1] = instance.fn
        byTarget[instance.target] = instance
    end
    local compilation = layouts.compilation
    local plan = Tail.prepare(functions, compilation.modules, compilation.foreigns)
    local queue, roots, buffers, order, edges, reports, analyses = {}, {}, {}, {}, {}, {}, {}
    local account = {weight = 0, limit = limit}
    local function requireRoot(target)
        if roots[target] then return end
        local instance = byTarget[target]
        if not instance then D.bug("c-root", "Missing residual root " .. target) end
        roots[target] = true
        queue[#queue + 1] = instance
    end
    for _, instance in ipairs(layouts.order) do
        if layouts.signatures[instance.target].exported then requireRoot(instance.target) end
    end
    local index = 1
    while index <= #queue do
        local instance = queue[index]
        index = index + 1
        local id = instance.target
        local unit = {plan=plan, newEmitter=newEmitter, analyses=analyses, requireRoot=requireRoot,
            active={}, depth=0, nextName=0, remaining=budget, weight=0, account=account,
            calls=0, jumps=0, expansions=0, edges={}, callReasons={}}
        local signature, args, lines = layouts.signatures[id], {}, {}
        for i, param in ipairs(signature.params) do args[i] = param.name end
        local component = plan.componentOf[id]
        M.group(layouts, unit, component, id, args, {exit=true}, lines, 1, false, true)
        if unit.weight > component.cost + budget then D.bug("c-budget", "Expansion exceeded its reserved credit") end
        buffers[#buffers + 1] = {signature=signature, lines=lines}
        order[#order + 1], edges[id] = id, unit.edges
        reports[#reports + 1] = {target=id, weight=unit.weight, mandatory=component.cost,
            calls=unit.calls, jumps=unit.jumps, expansions=unit.expansions, reasons=unit.callReasons}
    end
    local _, callComponents = Tail.components(order, edges)
    layouts.recursiveRoots = {}
    for _, id in ipairs(order) do layouts.recursiveRoots[id] = callComponents[id].cyclic end
    -- Keep the logical catalog/signatures for non-root component members and adapter bindings.
    layouts.instances, layouts.order = layouts.order, queue
    layouts.contextual = {reports=reports, budget=budget, weight=account.weight}
    return buffers
end

return M
