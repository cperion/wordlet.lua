-- Tail preparation over checked structured IR. No source evaluation and no node mutation.
local S = require("wordlet.schema")
local Walk = require("wordlet.walk")
local Check = require("wordlet.check")
local D = require("wordlet.diag")
local Ir = S.Ir
local M = {}

-- Iterative Kosaraju. Input/adjacency order is explicit; member and component order follow input.
-- Also used on the actual remaining C-call graph, not just the logical tail graph.
function M.components(order, edges)
    local reverse, seen, finish = {}, {}, {}
    for _, id in ipairs(order) do reverse[id] = {} end
    for _, id in ipairs(order) do
        for _, target in ipairs(edges[id] or {}) do
            if not reverse[target] then D.bug("tail-target", "Graph names unknown target " .. target) end
            reverse[target][#reverse[target] + 1] = id
        end
    end
    for _, start in ipairs(order) do
        if not seen[start] then
            seen[start] = true
            local stack = {{id = start, next = 1}}
            while #stack > 0 do
                local top = stack[#stack]
                local target = (edges[top.id] or {})[top.next]
                if target then
                    top.next = top.next + 1
                    if not seen[target] then
                        seen[target] = true
                        stack[#stack + 1] = {id = target, next = 1}
                    end
                else
                    finish[#finish + 1] = top.id
                    stack[#stack] = nil
                end
            end
        end
    end
    local byTarget = {}
    for i = #finish, 1, -1 do
        local start = finish[i]
        if not byTarget[start] then
            local group, stack = {entries = {}, cyclic = false}, {start}
            byTarget[start] = group
            while #stack > 0 do
                local id = table.remove(stack)
                for _, target in ipairs(reverse[id]) do
                    if not byTarget[target] then
                        byTarget[target] = group
                        stack[#stack + 1] = target
                    end
                end
            end
        end
    end
    local groups = {}
    for _, id in ipairs(order) do
        local group = byTarget[id]
        if not group.id then group.id = #groups + 1; groups[#groups + 1] = group end
        group.entries[#group.entries + 1] = id
        if #group.entries > 1 then group.cyclic = true end
        for _, target in ipairs(edges[id] or {}) do
            if id == target then group.cyclic = true end
        end
    end
    return groups, byTarget
end

-- Structural list traversal uses the generated fields. Semantic completion stays explicit below.
function M.lists(node, visit)
    -- The existing module initializer uses a plain function descriptor. Its body still consists
    -- of ASDL statements; enter that boundary explicitly, then use reflection for all children.
    if node.body and node.params and not (getmetatable(node) or {}).__fields then
        visit(node.body)
        for _, stmt in ipairs(node.body) do M.lists(stmt, visit) end
        return
    end
    for _, child in ipairs(Walk.children(node)) do
        if child.list and child.field.type == "Ir.Stmt" then
            visit(child.value)
            for _, stmt in ipairs(child.value) do M.lists(stmt, visit) end
        elseif child.list and child.field.type == "Ir.Case" then
            for _, case in ipairs(child.value) do M.lists(case, visit) end
        end
    end
end

local function walkFunction(fn, visitor)
    for _, param in ipairs(fn.params) do Walk.walk(param, visitor) end
    for _, stmt in ipairs(fn.body) do Walk.walk(stmt, visitor) end
end
local function scalar(ty) return ty and (ty:isInteger() or ty == S.bool or ty == S.f64) end
local SCALAR_STMTS = {Let=true, Var=true, Read=true, Store=true, Call=true, If=true,
    Switch=true, Loop=true, Next=true, Trap=true, Return=true,
    ConstructVariant=true, VariantMatches=true, VariantPayload=true}
local SCALAR_EXPRS = {Const=true, Ref=true, Un=true, Bin=true, Get=true, Make=true,
    Convert=true, SliceLength=true, Null=true}

-- A sufficient rule, not a general escape analysis: no invocation-owned address can be observed.
-- Unknown/new operations fail closed. Borrowed/aggregate cases keep ordinary calls.
function M.scalarOwner(fn)
    for _, param in ipairs(fn.params) do
        if param.kind ~= "ValueParam" or not scalar(param.type) then return false end
    end
    for _, ty in ipairs(fn.results) do if not scalar(ty) then return false end end
    local safe, seen = true, {}
    walkFunction(fn, {enter = function(node)
        if S.Ty.V:isclassof(node) then return false end
        if Ir.Expr:isclassof(node) then
            if seen[node] then return false end
            seen[node] = true
            if not SCALAR_EXPRS[node.kind] then safe = false end
        elseif Ir.Stmt:isclassof(node) and not SCALAR_STMTS[node.kind] then
            safe = false
        elseif node.kind == "BorrowArg" then
            safe = false
        end
        if node.type and not scalar(node.type) then safe = false end
    end})
    return safe
end

local function refTo(expr, value)
    return expr and expr.kind == "Ref" and expr.value.id == value.id
end
function M.identityReturn(call, ret)
    if not ret or ret.kind ~= "Return" or #call.results ~= #ret.values then return false end
    for i, value in ipairs(call.results) do if not refTo(ret.values[i], value) then return false end end
    return true
end
local function sameResults(a, b)
    if #a ~= #b then return false end
    for i, ty in ipairs(a) do if ty ~= b[i] then return false end end
    return true
end

local function mapControl(stmt, rewrite)
    if stmt.kind == "If" then
        local yes, no = rewrite(stmt.yes), rewrite(stmt.no)
        if not yes or not no then return nil end
        if yes == stmt.yes and no == stmt.no then return stmt end
        return Ir.If(stmt.test, yes, no)
    elseif stmt.kind == "Switch" then
        local cases, changed, tags = {}, false, {}
        -- A partial switch has an implicit continuing path; never invent its return value.
        if #stmt.cases ~= #S.alternatives(stmt.sum) then return nil end
        for _, case in ipairs(stmt.cases) do
            if tags[case.tag] or not S.caseOf(stmt.sum, case.tag) then return nil end
            tags[case.tag] = true
            local body = rewrite(case.body)
            if not body then return nil end
            changed = changed or body ~= case.body
            cases[#cases + 1] = Ir.Case(case.tag, case.fallback, S.list(body))
        end
        return changed and Ir.Switch(stmt.variant, stmt.sum, S.list(cases)) or stmt
    end
end

-- Turn exact private join transports into existing Return nodes. Every use of a removed slot must
-- be accounted for. This never hoists a read, call, trap, or payload projection across a branch.
function M.normalize(fn)
    if not M.scalarOwner(fn) then return fn end
    local declarations, uses = {}, {}
    M.lists(fn, function(list)
        for _, stmt in ipairs(list) do
            if stmt.kind == "Var" then declarations[stmt.storage.id] = stmt end
            local seen = {}
            Walk.walk(stmt, {enter = function(node)
                if S.Ty.V:isclassof(node) or (Ir.Stmt:isclassof(node) and node ~= stmt) then return false end
                if Ir.Expr:isclassof(node) then
                    if seen[node] then return false end
                    seen[node] = true
                end
                if node.kind == "Local" then
                    local id = node.storage.id
                    uses[id] = uses[id] or {}
                    uses[id][stmt] = (uses[id][stmt] or 0) + 1
                end
            end})
        end
    end)
    local function join(list)
        local ret = list[#list]
        if not ret or ret.kind ~= "Return" then return list end
        local n = #ret.values
        local at = #list - n - 1
        local control = list[at]
        if not control or (control.kind ~= "If" and control.kind ~= "Switch") then return list end
        local slots, allowed, removing, present = {}, {}, {}, {}
        for i = 1, at - 1 do present[list[i]] = true end
        for i, value in ipairs(ret.values) do
            local read = list[at + i]
            if read.kind ~= "Read" or read.place.kind ~= "Local" or not refTo(value, read.value) then return list end
            local id = read.place.storage.id
            local decl = declarations[id]
            if slots[id] or not decl or decl.initial or not present[decl] or not scalar(decl.type) then return list end
            slots[id], allowed[id], removing[decl] = i, {[read] = true}, true
        end
        local function arm(body)
            local last = body[#body]
            -- Trap is conditional and is deliberately not in this terminating set.
            if last and (last.kind == "Return" or last.kind == "Next" or last.kind == "Loop") then return body end
            if last and (last.kind == "If" or last.kind == "Switch") then
                local nested = mapControl(last, arm)
                if not nested then return nil end
                local out = {}
                for i = 1, #body - 1 do out[i] = body[i] end
                out[#out + 1] = nested
                return S.list(out)
            end
            if #body < n then return nil end
            local values, out = {}, {}
            for i = #body - n + 1, #body do
                local store = body[i]
                if store.kind ~= "Store" or store.place.kind ~= "Local" then return nil end
                local id = store.place.storage.id
                local index = slots[id]
                if not index or values[index] then return nil end
                values[index], allowed[id][store] = store.value, true
            end
            for i = 1, #body - n do out[i] = body[i] end
            out[#out + 1] = Ir.Return(S.list(values))
            return S.list(out)
        end
        local rewritten = mapControl(control, arm)
        if not rewritten then return list end
        for id in pairs(slots) do
            for stmt, count in pairs(uses[id] or {}) do
                if not allowed[id][stmt] or count ~= 1 then return list end
            end
        end
        local out = {}
        for i = 1, at - 1 do if not removing[list[i]] then out[#out + 1] = list[i] end end
        out[#out + 1] = rewritten
        return S.list(out)
    end
    local normalizeList
    normalizeList = function(list)
        local current = join(list)
        local out, changed = {}, current ~= list
        for _, stmt in ipairs(current) do
            local replacement = stmt
            if stmt.kind == "If" or stmt.kind == "Switch" then
                replacement = mapControl(stmt, normalizeList) or stmt
            elseif stmt.kind == "Loop" then
                local body = normalizeList(stmt.body)
                if body ~= stmt.body then replacement = Ir.Loop(S.list(body)) end
            end
            changed = changed or replacement ~= stmt
            out[#out + 1] = replacement
        end
        return changed and S.list(out) or list
    end
    local body = normalizeList(fn.body)
    if body == fn.body then return fn end
    return Ir.Fn(fn.id, fn.role, fn.hidden, S.list(fn.inputs), S.list(fn.results), S.list(fn.params), S.list(body))
end

local function weight(fn)
    local count, seen = 1, {}
    walkFunction(fn, {enter = function(node)
        if S.Ty.V:isclassof(node) then return false end
        if Ir.Expr:isclassof(node) then
            if seen[node] then return false end
            seen[node] = true
        end
        count = count + 1
    end})
    return math.max(1, count)
end

function M.prepare(functions, modules, foreigns)
    local plan = {functions = {}, tailSites = {}, costs = {}, order = {}, safe = {}}
    local checked, changed, edges = {}, false, {}
    for _, original in ipairs(functions) do
        local fn = M.normalize(original)
        checked[#checked + 1] = fn
        changed = changed or fn ~= original
        plan.functions[fn.id], plan.safe[fn.id], plan.costs[fn.id] = fn, M.scalarOwner(fn), weight(fn)
        plan.order[#plan.order + 1] = fn.id
        edges[fn.id] = {}
    end
    if changed then Check.program(checked, modules, foreigns) end
    for _, id in ipairs(plan.order) do
        local fn = plan.functions[id]
        M.lists(fn, function(list)
            local call, ret = list[#list - 1], list[#list]
            if call and call.kind == "Call" and plan.safe[id] and plan.safe[call.target]
                and M.identityReturn(call, ret) and sameResults(fn.results, plan.functions[call.target].results) then
                plan.tailSites[call] = {owner = id, list = list, index = #list - 1, returned = ret}
                edges[id][#edges[id] + 1] = call.target
            end
        end)
    end
    plan.components, plan.componentOf = M.components(plan.order, edges)
    for _, group in ipairs(plan.components) do
        group.cost = 0
        for _, id in ipairs(group.entries) do group.cost = group.cost + plan.costs[id] end
    end
    return plan
end

return M
