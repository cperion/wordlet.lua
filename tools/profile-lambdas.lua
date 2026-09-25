-- Bounded investigation of lambda construction on the REAL evaluator; no memo or skipped work.
-- Usage: luajit tools/profile-lambdas.lua [MAX_N [KEYS [STEPS]]]
-- CPU timings include instrumentation. Capture-shape counts are diagnostic, NOT safe cache keys.
local path = debug.getinfo(1, "S").source:sub(2)
local root = (path:match("^(.*[/\\])") or "./") .. "../"
package.path = root .. "?.lua;" .. root .. "?/init.lua;" .. package.path
local Eval = require("wordlet.eval")
local Parse = require("wordlet.parse")
local V = require("wordlet.value")
local S = require("wordlet.schema")
local D = require("wordlet.diag")

local function option(index, default)
    local value = tonumber(arg[index] or default)
    assert(value and value >= 0 and value % 1 == 0, "expected a finite nonnegative integer option")
    return value
end
local maximum, keys, steps = option(1, 4), option(2, 65536), option(3, 10000000)
assert(not arg[4], "usage: profile-lambdas.lua [MAX_N [KEYS [STEPS]]]")
local limits = {keys=keys, steps=steps, staticDepth=1024, depth=1024, interpretDepth=4096}

local fixtures = {
    {name="match", tracked="vm", source=[[
let Op=oneof {step:unit,branch:unit,halt:unit}
let instruction(pc:u32):Op=[Op.step(),Op.branch(),Op.halt()][pc]
let vm(pc,n,a:u32):u32=instruction(pc){
 step=|u:unit|->vm(pc+1,n,a+3),
 branch=|u:unit|->if n==0 then vm(pc+1,n,a) else vm(0,n-1,a),
 halt=|u:unit|->a,
}
let run(n,a:u32):u32=vm(0,n,a)
return {functions={run}}
]], args=function(n) return {V.u32(n), V.u32(7)} end, expected=function(n) return 7+3*(n+1) end},
    -- Equivalent concrete transitions without constructing handler lambdas.
    {name="direct", tracked="vm", source=[[
let vm(pc,n,a:u32):u32=if pc==0 then vm(pc+1,n,a+3)
 else if pc==1 then if n==0 then vm(pc+1,n,a) else vm(0,n-1,a)
 else a
let run(n,a:u32):u32=vm(0,n,a)
return {functions={run}}
]], args=function(n) return {V.u32(n), V.u32(7)} end, expected=function(n) return 7+3*(n+1) end},
    -- No match or sum at all: an immediately invoked lambda reproduces the repeated suffix work.
    -- Depth 2*n+2 gives the same number of logical word invocations as the VM fixture.
    {name="lambda-chain", tracked="chain", source=[[
let chain(n:u32):u32=if n==0 then 0 else (|u:unit|->chain(n-1)+1)(unit())
let run(n:u32):u32=chain(n)
return {functions={run}}
]], args=function(n) return {V.u32(2*n+2)} end, expected=function(n) return 2*n+2 end},
}

local function instrument(e, tracked)
    local stats = {origins={}, byNode={}, words=0, wordsInBuild=0, requests=0, definitions=0,
        builds=0, invokes=0, shapes=0}
    local function origin(node)
        local info = stats.byNode[node]
        if not info then
            info = {node=node, definitions=0, builds=0, invokes=0, shapes=0, seen={}}
            stats.byNode[node] = info
            stats.origins[#stats.origins+1] = info
        end
        return info
    end
    -- Override only this session, leaving the shared Eval class and other sessions untouched.
    function e:define(node, ...)
        if node.kind == "Lambda" then
            local info = origin(node)
            info.definitions = info.definitions + 1
            stats.definitions = stats.definitions + 1
        end
        return Eval.define(self, node, ...)
    end
    function e:prepareLambdaCPS(machine, ctx, expr, expected, k)
        local info = origin(expr)
        return Eval.prepareLambdaCPS(self, machine, ctx, expr, expected, function(m, plan)
            -- Preparation has parameter types but NO claimed result signature. Group by origin,
            -- captures and input/environment shape, ignoring only the fresh lambda id prefix.
            -- This deliberately does NOT prove scope, borrow, alias or metadata safety for reuse.
            local parts = {plan.key:gsub("^closure:%d+", ""), S.encode(plan.envTy)}
            for _, ty in ipairs(plan.paramTypes) do parts[#parts+1] = S.encode(ty) end
            for _, name in ipairs(plan.order) do
                local capture = plan.static[name]
                parts[#parts+1] = name .. ":literal=" .. tostring(capture and capture.literal)
            end
            local shape = table.concat(parts, "\n")
            if not info.seen[shape] then
                info.seen[shape] = true
                info.shapes, stats.shapes = info.shapes+1, stats.shapes+1
            end
            return k(m, plan)
        end)
    end
    function e:callableInstanceCPS(machine, callable, args, span, k)
        stats.requests = stats.requests + 1
        return Eval.callableInstanceCPS(self, machine, callable, args, span, k)
    end
    function e:constructCallableInstanceCPS(machine, key, callable, args, span, k)
        local info = origin(callable.plan.def.node)
        stats.builds, info.builds = stats.builds+1, info.builds+1
        return Eval.constructCallableInstanceCPS(self, machine, key, callable, args, span, k)
    end
    function e:evaluateClosureStaticallyCPS(machine, plan, args, span, k)
        local info = origin(plan.def.node)
        stats.invokes, info.invokes = stats.invokes+1, info.invokes+1
        return Eval.evaluateClosureStaticallyCPS(self, machine, plan, args, span, k)
    end
    function e:evaluateStaticallyCPS(machine, def, args, span, receiver, k)
        if def.name == tracked then
            stats.words = stats.words + 1
            for _, descriptor in ipairs(machine.descriptors) do
                if descriptor.kind == "build" then
                    stats.wordsInBuild = stats.wordsInBuild + 1
                    break
                end
            end
        end
        return Eval.evaluateStaticallyCPS(self, machine, def, args, span, receiver, k)
    end
    return stats
end

local function profile(fixture, n)
    collectgarbage("collect")
    local e = Eval.new{limits=limits}
    local stats = instrument(e, fixture.tracked)
    local started = os.clock()
    -- The same load/initialize/export/supply entries used by wordlet.interpret. Calling them
    -- directly lets the tool instrument ONE owned session, without a process-global monkeypatch.
    local ok, result = pcall(function()
        local program = Parse.source(fixture.source, fixture.name .. ".let")
        e.run = true
        local top = e:load(program)
        e:initializeModule(program, top)
        local word = e:exportedTop(program, "run", top)
        return e:supplyTop(e:staticFrame(top, word.span), word, fixture.args(n), word.span)
    end)
    local elapsed = os.clock() - started
    if ok then assert(V.tag(result)=="int" and result.n==fixture.expected(n), "wrong fixture result") end
    print(("%s n=%d result=%s words=%d in_build=%d lambda_defs=%d instance_requests=%d "
        .. "lambda_builds=%d lambda_invokes=%d shapes=%d instances=%d steps=%d CPU=%.6fs")
        :format(fixture.name, n, ok and tostring(result.n) or "ERROR", stats.words, stats.wordsInBuild,
            stats.definitions, stats.requests, stats.builds, stats.invokes, stats.shapes,
            e.instanceCount, e.steps, elapsed))
    table.sort(stats.origins, function(a,b) return a.node.span.start < b.node.span.start end)
    for _, info in ipairs(stats.origins) do
        print(("  lambda line=%d byte=%d definitions=%d builds=%d invokes=%d shapes=%d")
            :format(info.node.span.line, info.node.span.start, info.definitions,
                info.builds, info.invokes, info.shapes))
    end
    if not ok then
        io.stderr:write(D.is(result) and D.format(result) or tostring(result), "\n")
        return false
    end
    return true
end

print(("limits: keys=%d steps=%d staticDepth=1024 depth=1024 interpretDepth=4096; NO memo or skipped work")
    :format(keys, steps))
for n=0,maximum do
    for _, fixture in ipairs(fixtures) do
        if not profile(fixture,n) then os.exit(1) end
    end
end
