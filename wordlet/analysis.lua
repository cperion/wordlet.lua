-- The facts one `Ir.Fn`'s emission needs, computed once. Every analysis here is per function: the
-- builder interns `Ir.Expr` per function, so a value id, a storage id and an expression node mean one
-- thing only inside the function that owns them (structure.md §1.2). The names follow §3.5.
--
-- One walk over the statements collects every fact, because the five walks that came before wanted
-- the same information: which storages a place names, which values a `Ref` names, which storages a
-- store, an address or a borrow mutates, how often each value is read, which statement defines each
-- value, and the expression roots of each statement with its place in its list. The two rules that
-- are not a collection — which single-use definition may be inlined, and where a shared expression
-- has to be declared — run afterwards over those collected facts.
--
-- The walk is an explicit visitor, not a reflective one: what a `Store` mutates, that a `Ref` names a
-- value and that a `Switch` reads its variant are semantic facts, and `ASDL.md` keeps those in the
-- pass that owns them. Only the recursion into a place's or an expression's children is structural.
local S = require("wordlet.schema")

local M = {}

-- The expressions a node hands over as it is printed. `Ir.Expr:each` states that per variant, and a
-- place operand contributes the expressions reaching it.
local function collectExprs(expr, out)
    expr:each(function(child) out[#out + 1] = child end)
end

local eachExpr, eachPlace

-- A place is visited as a place, then its base chain, then the expressions reaching it: marking that
-- a `Local` names a storage, and finding the root a store writes through, need the node itself, which
-- `Ir.Place:each` does not hand over.
eachPlace = function(place, visit, root)
    if not place then return end
    visit.place(place)
    local kind = place.kind
    if kind == "Project" or kind == "Deref" then
        eachPlace(place.base, visit, root)
    elseif kind == "Index" then
        eachPlace(place.base, visit, root)
        eachExpr(place.index, visit, root)
    elseif kind == "SliceIndex" or kind == "PtrIndex" then
        -- A slice or pointer element names a view value rather than a local root, so it is not a
        -- place a store can root at. Its expressions are still visited.
        eachExpr(place.view, visit, root)
        eachExpr(place.index, visit, root)
    end
end

eachExpr = function(expr, visit, root)
    if not expr then return end
    if root then visit.root(expr) end
    visit.expr(expr)
    -- `Addr:each` hands the expressions of the place it addresses, but the place itself is where a
    -- storage is named, so the place is visited as a place here (which reaches those same
    -- expressions, in the same order).
    if expr.kind == "Addr" then return eachPlace(expr.place, visit, false) end
    expr:each(function(child) eachExpr(child, visit, false) end)
end

-- The places and expressions one statement mentions, in the order the emitter prints them. This is
-- the one statement switch that is not the emitter's own: every analysis below reads its result
-- instead of walking the statements again.
local function eachStatement(stmt, visit)
    local kind = stmt.kind
    local function arguments(list)
        for _, arg in ipairs(list) do
            if arg.kind == "ValueArg" then
                eachExpr(arg.value, visit, true)
            else
                visit.borrow(arg.place)
                eachPlace(arg.place, visit, true)
            end
        end
    end
    if kind == "Let" then eachExpr(stmt.expr, visit, true)
    elseif kind == "Var" then eachExpr(stmt.initial, visit, true)
    elseif kind == "Read" then eachPlace(stmt.place, visit, true)
    elseif kind == "Store" then
        visit.store(stmt)
        eachPlace(stmt.place, visit, true)
        eachExpr(stmt.value, visit, true)
    elseif kind == "View" then arguments(stmt.slots)
    elseif kind == "Call" then arguments(stmt.arguments)
    elseif kind == "Indirect" then
        eachExpr(stmt.callable, visit, true)
        arguments(stmt.arguments)
    elseif kind == "If" then eachExpr(stmt.test, visit, true)
    elseif kind == "Trap" then eachExpr(stmt.failure, visit, true)
    elseif kind == "ConstructVariant" then eachExpr(stmt.payload, visit, true)
    elseif kind == "Return" then
        for _, value in ipairs(stmt.values) do eachExpr(value, visit, true) end
    end
end

-- The statement lists nested in one statement, in the order the emitter prints them: an arm is part
-- of the enclosing body, so the walk enters it where the statement stands.
local function eachNested(stmt, visit, entry)
    local kind = stmt.kind
    if kind == "If" then
        visit.list(stmt.yes, entry)
        visit.list(stmt.no, entry)
    elseif kind == "Loop" then
        visit.list(stmt.body, entry)
    elseif kind == "Switch" then
        for _, case in ipairs(stmt.cases) do visit.list(case.body, entry) end
    end
end

function M.analyze(fn)
    local analysis = {
        -- structure.md §3.5
        storageUses = {},     -- storage id -> true: a place names it, so its `Var` is printed
        valueUses = {},       -- value id -> true: a `Ref` names it, so its `Read` is not dropped
        mutatedStorages = {}, -- storage id -> true: written, borrowed or addressed
        paramValues = {},     -- value id -> true: a by-value parameter binding
        useCount = {},        -- value id -> how many `Ref` expressions read it
        inline = {},          -- value id -> { stmt } | { place }: the one use it moves to
        shared = {},          -- Ir.Expr -> true: printed more than once, so bound to one local
        sharedDecls = {},     -- Ir.Stmt list -> index -> the shared expressions to bind before it
    }
    -- Facts the rules below need and the emitter does not.
    local defs = {}           -- value id -> the statement that defines it
    local reads = {}          -- statement -> the value ids it reads
    local sites = {}          -- every statement list, in the order the walk entered it
    local current

    -- The root of a place: the local storage a store or an address reaches through projections and
    -- index expressions. Anything else names a view value rather than a local root.
    local function rootOf(place)
        while place do
            if place.kind == "Local" then return place.storage.id end
            if place.kind == "Project" or place.kind == "Deref" or place.kind == "Index" then
                place = place.base
            else
                return nil
            end
        end
        return nil
    end

    -- Declared before the table so the visitor's own functions capture the local: inside the
    -- constructor `visit` would still name an outer (or global) binding.
    local visit
    visit = {
        list = function(list, parentEntry)
            local site = { list = list, statements = {} }
            sites[#sites + 1] = site
            for index, stmt in ipairs(list) do
                -- A path is the list a statement is in plus its index, and the enclosing statement's
                -- path: the innermost list holding every use of a shared node is chosen from these.
                local entry = { stmt = stmt, index = index, site = site, roots = {},
                    path = { list = list, index = index,
                        parent = parentEntry and parentEntry.path or nil } }
                site.statements[#site.statements + 1] = entry
                current = entry
                local kind = stmt.kind
                reads[stmt] = {}
                if kind == "Let" or kind == "Read" or kind == "ConstructVariant"
                    or kind == "VariantMatches" or kind == "VariantPayload" then
                    defs[stmt.value.id] = stmt
                end
                if kind == "VariantMatches" or kind == "VariantPayload" or kind == "Switch" then
                    -- The variant is read by the statement itself rather than by a `Ref`, so it is
                    -- a read a pending `Read` can move to as well.
                    local id = stmt.variant.id
                    analysis.valueUses[id] = true
                    analysis.useCount[id] = (analysis.useCount[id] or 0) + 1
                    reads[stmt][id] = true
                end
                eachStatement(stmt, visit)
                eachNested(stmt, visit, entry)
                current = nil
            end
        end,
        place = function(place)
            if place.kind == "Local" then analysis.storageUses[place.storage.id] = true end
        end,
        -- A store, a borrow and an address all make a storage mutable, and all three name it by the
        -- root they reach through.
        store = function(stmt)
            local id = rootOf(stmt.place)
            if id then analysis.mutatedStorages[id] = true end
        end,
        borrow = function(place)
            local id = rootOf(place)
            if id then analysis.mutatedStorages[id] = true end
        end,
        root = function(expr)
            if current then current.roots[#current.roots + 1] = expr end
        end,
        expr = function(expr)
            if expr.kind == "Ref" then
                local id = expr.value.id
                analysis.valueUses[id] = true
                analysis.useCount[id] = (analysis.useCount[id] or 0) + 1
                if current then reads[current.stmt][id] = true end
            elseif expr.kind == "Addr" then
                local id = rootOf(expr.place)
                if id then analysis.mutatedStorages[id] = true end
            end
        end,
    }

    for _, param in ipairs(fn.params or {}) do
        if param.kind == "ValueParam" and param.binding then
            analysis.paramValues[param.binding.id] = true
        end
    end
    visit.list(fn.body)

    -- A definition with one use is lowered where it is used instead of through a local. A pure
    -- definition may move to its use freely; a `Read` is a snapshot of storage, so it may only move to
    -- a use that no store or call can reach in between. This is how the evaluator's explicit
    -- definitions become expressions at emission, not a general optimizer.
    local function effectful(stmt)
        local kind = stmt.kind
        return kind == "Store" or kind == "Call" or kind == "Indirect"
            or kind == "If" or kind == "Loop" or kind == "Switch"
    end
    for id, stmt in pairs(defs) do
        if analysis.useCount[id] == 1 and (stmt.kind == "Let" or stmt.kind == "ConstructVariant"
            or stmt.kind == "VariantMatches" or stmt.kind == "VariantPayload") then
            analysis.inline[id] = { stmt = stmt }
        end
    end
    -- A `Read` may move to its single use only within its own list, and only past pure statements: a
    -- store or a call can change what the place it read would yield.
    for _, site in ipairs(sites) do
        local pending = {}
        for _, entry in ipairs(site.statements) do
            local stmt = entry.stmt
            -- The test of an `If` runs as part of the statement, so it is not a use a pending `Read`
            -- may move to; the two arm lists are scanned as their own lists. This is the rule the
            -- emitter had before the walks were consolidated, and the emitted C depends on it.
            local used = stmt.kind == "If" and {} or reads[stmt]
            for id in pairs(used) do
                if pending[id] and analysis.useCount[id] == 1 then
                    analysis.inline[id] = { place = pending[id] }
                    pending[id] = nil
                end
            end
            if stmt.kind == "Read" then pending[stmt.value.id] = stmt.place end
            if effectful(stmt) then
                for id in pairs(pending) do pending[id] = nil end
            end
        end
    end

    -- The IR is a DAG: `Builder:intern` unifies structurally equal expressions, so one node can be
    -- referenced many times, and `Emitter:render` is a tree walk that would print every reference.
    -- This finds the nodes used more than once and the innermost statement list containing all of
    -- their uses, so the emitter can bind each to one local and print names instead.
    --
    -- A `Var` or `Read` the emitter drops contributes no printed expression, so it must not make a
    -- construction expression look shared: counting it would name a copy of an expression that the
    -- dead declaration never prints.
    local function dropped(stmt)
        if stmt.kind == "Var" then return not analysis.storageUses[stmt.storage.id] end
        if stmt.kind == "Read" then return not analysis.valueUses[stmt.value.id] end
        return false
    end
    local seen, nodes, edges, roots = {}, {}, {}, {}
    local paths, pathList, chains = {}, {}, {}

    local function chainOf(path)
        local chain = chains[path]
        if chain then return chain end
        local reversed = {}
        local node = path
        while node do reversed[#reversed + 1] = node; node = node.parent end
        chain = {}
        for index = #reversed, 1, -1 do chain[#chain + 1] = reversed[index] end
        chains[path] = chain
        return chain
    end

    local function collect(expr)
        if not expr or seen[expr] then return end
        seen[expr] = true
        nodes[#nodes + 1] = expr
        local children = {}
        collectExprs(expr, children)
        local list, position = {}, {}
        for _, child in ipairs(children) do
            if not position[child] then
                position[child] = #list + 1
                list[#list + 1] = { node = child, count = 0 }
            end
            list[position[child]].count = list[position[child]].count + 1
        end
        edges[expr] = list
        for _, edge in ipairs(list) do collect(edge.node) end
    end

    for _, site in ipairs(sites) do
        for _, entry in ipairs(site.statements) do
            if not dropped(entry.stmt) then
                for _, expr in ipairs(entry.roots) do
                    if expr then
                        collect(expr)
                        roots[#roots + 1] = { node = expr, path = entry.path }
                    end
                end
            end
        end
    end

    -- Reference counts and use positions propagate from the statement roots through the DAG, so the
    -- walk is linear in the DAG and never expands the shared tree.
    local order, marked = {}, {}
    local function orderVisit(node)
        if marked[node] then return end
        marked[node] = true
        for _, edge in ipairs(edges[node]) do orderVisit(edge.node) end
        order[#order + 1] = node
    end
    for _, root in ipairs(roots) do orderVisit(root.node) end

    local uses = {}
    for _, root in ipairs(roots) do
        uses[root.node] = math.min(2, (uses[root.node] or 0) + 1)
        if not paths[root.node] then paths[root.node] = {}; pathList[root.node] = {} end
        if not paths[root.node][root.path] then
            paths[root.node][root.path] = true
            pathList[root.node][#pathList[root.node] + 1] = root.path
        end
    end
    for index = #order, 1, -1 do
        local node = order[index]
        local count = uses[node] or 0
        if count > 0 then
            for _, edge in ipairs(edges[node]) do
                local child = edge.node
                uses[child] = math.min(2, (uses[child] or 0) + count * edge.count)
                if pathList[node] then
                    if not paths[child] then paths[child] = {}; pathList[child] = {} end
                    for _, path in ipairs(pathList[node]) do
                        if not paths[child][path] then
                            paths[child][path] = true
                            pathList[child][#pathList[child] + 1] = path
                        end
                    end
                end
            end
        end
    end

    for _, node in ipairs(nodes) do
        if uses[node] and uses[node] >= 2 and node.kind ~= "Const" and node.kind ~= "Ref" then
            analysis.shared[node] = true
            local list = pathList[node]
            local first = chainOf(list[1])
            local depth = #first
            for _, path in ipairs(list) do
                local chain = chainOf(path)
                local matched = 0
                while matched < depth and matched < #chain
                    and chain[matched + 1].list == first[matched + 1].list do
                    matched = matched + 1
                end
                if matched < depth then depth = matched end
            end
            local target = first[depth].list
            local earliest = first[depth].index
            for _, path in ipairs(list) do
                local index = chainOf(path)[depth].index
                if index < earliest then earliest = index end
            end
            analysis.sharedDecls[target] = analysis.sharedDecls[target] or {}
            analysis.sharedDecls[target][earliest] = analysis.sharedDecls[target][earliest] or {}
            local pending = analysis.sharedDecls[target][earliest]
            pending[#pending + 1] = node
        end
    end
    return analysis
end

return M
