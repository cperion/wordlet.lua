-- Tail components and optional residual copies, checked independently of host tail/inlining opts.
local sourcePath = debug.getinfo(1, "S").source:sub(2)
local root = (sourcePath:match("^(.*[/\\])") or "./") .. "../"
package.path = root .. "?.lua;" .. root .. "?/init.lua;" .. package.path
local W = require("wordlet")
local S = require("wordlet.schema")
local IR = require("wordlet.ir")
local Tail = require("wordlet.tail")
local Check = require("wordlet.check")
local C = require("wordlet.cabi")
local Lower = require("wordlet.lower")
local Walk = require("wordlet.walk")
local Ir = S.Ir
local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end
local function q(text) return "'" .. text:gsub("'", "'\\''") .. "'" end
local function write(path, text)
    local f = assert(io.open(path, "wb")); assert(f:write(text)); assert(f:close())
end
local function read(path)
    local f = assert(io.open(path, "rb")); local text = f:read("*a"); f:close(); return text
end
local function command(text) return os.execute(text) == 0 end

-- SCC work consumes an explicit stack, including a long acyclic prefix and a large cycle.
do
    local order, edges = {}, {}
    for i = 1, 12000 do order[i] = "g" .. i; edges[order[i]] = {"g" .. (i + 1)} end
    edges.g12000 = {"g6001"}
    local groups, by = Tail.components(order, edges)
    check(#groups == 6001 and #by.g6001.entries == 6000 and by.g6001.cyclic, "iterative SCC closure")
    check(not by.g1.cyclic and by.g1.id == 1 and by.g12000 == by.g6001, "stable component ordering")
end

-- Build the exact diamond using real ASDL. A later unrelated use of the slot blocks elimination.
local function diamond(extraUse)
    local b = IR.builder()
    local p = b:valueId()
    local slot = b:storageId()
    local v = b:valueId()
    local yes = {Ir.Store(Ir.Local(slot), b:u32(11))}
    if extraUse then
        yes[#yes + 1] = Ir.Read(b:valueId(), S.U32, Ir.Local(slot))
        yes[#yes + 1] = Ir.Store(Ir.Local(slot), b:u32(11))
    end
    local fn = Ir.Fn("diamond", Ir.Entry, 0, S.list{S.inValue(S.Bool)}, S.list{S.U32},
        S.list{Ir.ValueParam(0, p, S.Bool)}, S.list{
            Ir.Var(slot, S.U32, nil),
            Ir.If(b:ref(p, S.Bool), S.list(yes), S.list{Ir.Store(Ir.Local(slot), b:u32(22))}),
            Ir.Read(v, S.U32, Ir.Local(slot)), Ir.Return(S.list{b:ref(v, S.U32)})})
    return fn
end
do
    local fn = diamond(false)
    Check.program({fn})
    local changed = Tail.normalize(fn)
    Check.program({changed})
    check(changed ~= fn and #changed.body == 1 and changed.body[1].yes[1].kind == "Return", "private join becomes returns")
    check(#fn.body == 4 and fn.body[2].yes[1].kind == "Store", "normalization preserves the original template")
    local blocked = diamond(true)
    Check.program({blocked})
    check(Tail.normalize(blocked) == blocked, "unaccounted slot use prevents normalization")
    local b = IR.builder()
    local value = b:valueId()
    check(Tail.identityReturn(Ir.Call(S.list{value}, "f", S.list{}), Ir.Return(S.list{b:ref(value, S.U32)})), "exact identity return")
    check(not Tail.identityReturn(Ir.Call(S.list{value}, "f", S.list{}), Ir.Return(S.list{b:bin("Add", b:ref(value,S.U32), b:u32(1), S.U32)})), "result work is not a tail")
end

-- Multiple-result join transport is checked directly as IR as well as source expression/statement tails.
do
    local b = IR.builder()
    local p = b:valueId()
    local a, z = b:storageId(), b:storageId()
    local x, y = b:valueId(), b:valueId()
    local fn = Ir.Fn("pair_join", Ir.Entry, 0, S.list{S.inValue(S.Bool)}, S.list{S.U32,S.U32},
        S.list{Ir.ValueParam(0,p,S.Bool)}, S.list{
            Ir.Var(a,S.U32,nil), Ir.Var(z,S.U32,nil),
            Ir.If(b:ref(p,S.Bool),
                S.list{Ir.Store(Ir.Local(a),b:u32(1)),Ir.Store(Ir.Local(z),b:u32(2))},
                S.list{Ir.Store(Ir.Local(z),b:u32(4)),Ir.Store(Ir.Local(a),b:u32(3))}),
            Ir.Read(x,S.U32,Ir.Local(a)),Ir.Read(y,S.U32,Ir.Local(z)),
            Ir.Return(S.list{b:ref(x,S.U32),b:ref(y,S.U32)})})
    Check.program({fn})
    local normalized = Tail.normalize(fn)
    Check.program({normalized})
    check(#normalized.body==1 and #normalized.body[1].no[1].values==2, "vector join normalization")
    check(normalized.body[1].no[1].values[1].literal.value==3, "return order is independent of slot store order")
    local aggregate = Ir.Fn("unsafe_owner",Ir.Body,0,S.list{},S.list{},S.list{},
        S.list{Ir.Var(b:storageId(),S.array(S.U32,2),nil),Ir.Return(S.list{})})
    check(not Tail.scalarOwner(aggregate), "aggregate-owned activation cannot reuse scalar carriers")
end

local program = [[
let even(n: U32): Bool = if n==0 then true else odd(n-1)
let odd(n: U32): Bool = if n==0 then false else even(n-1)
let nested_a(n: U32): Bool = if n==0 then true else if n==1 then false else nested_b(n-1)
let nested_b(n: U32): Bool = if n==0 then false else nested_a(n-1)
let cycle_a(n,a,b: U32): U32 = do
  if n==0 then return a*100+b end
  return cycle_b(b,a,n-1,n!=0)
end
let cycle_b(a,b,n: U32, unused: Bool): U32 = do
  if n==0 then return a*100+b end
  return cycle_c(n-1,b,a)
end
let cycle_c(n,a,b: U32): U32 = do
  if n==0 then return a*100+b end
  return cycle_a(n-1,b,a)
end
let pair_base(a,b: U32): (U32,U32) = do return a,b end
let pair_a(n,a,b: U32): (U32,U32) = if n==0 then pair_base(a,b) else pair_b(n-1,b,a)
let pair_b(n,a,b: U32): (U32,U32) = do
  if n==0 then return pair_base(a,b) end
  return pair_a(n-1,b,a)
end
let State = {n: U32}
let state = State {n=0}
let set(n: U32): Unit = do state.n=n return end
let get(): U32 = state.n
let read_callback: (): U32 = || -> get()
let via_callback(): U32 = read_callback()
let bump(): U32 = do state.n+=1 return state.n end
let delayed: (): U32 = || -> bump()
let via_delayed(): U32 = delayed()
let module_a(): Unit = do
  if get()==0 then return end
  state.n-=1
  return module_b()
end
let module_b(): Unit = do
  if get()==0 then return end
  state.n-=1
  return module_a()
end
let nested_self(n,a: U32): U32 = if n==0 then a else if n%2==0 then nested_self(n-1,a+1) else nested_self(n-1,a+2)
let known_self(n,a: U32): U32 = if true then if n==0 then a else known_self(n-1,a+1) else 0
let mixed_pair(x: U32): (Unit,U32,Unit,U32) = do return Unit(),x,Unit(),x+1 end
let mixed_choose(flag: Bool,x: U32): (Unit,U32,Unit,U32) = if flag then mixed_pair(x) else mixed_pair(x+10)
let effect_pair(n: U32): (U32,U32) = do state.n=state.n*10+n return state.n,state.n+1 end
let effect_choose(flag: Bool): (U32,U32) = if flag then effect_pair(2) else effect_pair(3)
let signed_zero(flag: Bool): F64 = if flag then 0.0 else -0.0
let VMOp=OneOf({step:Unit,branch:Unit,halt:Unit})
let instruction(pc:U32):VMOp=[VMOp.step(),VMOp.branch(),VMOp.halt()][pc]
let vm(pc,n,a:U32):U32=instruction(pc){
  step=|u:Unit|->vm(pc+1,n,a+3),
  branch=|u:Unit|->if n==0 then vm(pc+1,n,a) else vm(0,n-1,a),
  halt=|u:Unit|->a,
}
let static_pc(n,a:U32):U32=vm(0,n,a)
extern let host_more(): Bool
let null_a(): Unit = do
  if not host_more() then return end
  return null_b()
end
let null_b(): Unit = do
  if not host_more() then return end
  return null_a()
end
let mixed_a(n: U32): U32 = if n==0 then 0 else n+mixed_b(n-1)
let mixed_b(n: U32): U32 = if n==0 then 0 else mixed_a(n-1)
let Box = {value: U32, read(): U32 = value}
let through {f: (): U32, n: U32}: U32 = if n==0 then f() else walk(n-1)+f()
let walk(n: U32): U32 = do
  let b = Box {value=n}
  return through {f=b.read,n=n}
end
let record(n: U32): Unit = do state.n+=n return end
let defer_a(n: U32): U32 = do
  defer record(n)
  if n==0 then return 0 end
  return defer_b(n-1)
end
let defer_b(n: U32): U32 = do
  defer record(n)
  if n==0 then return 0 end
  return defer_a(n-1)
end
let j(x: U32): U32 = x*3+1
let h(x: U32): U32 = j(x)+j(x+1)
let helper_a(x,y: U32): U32 = h(x)+h(y)
let helper_b(x: U32): U32 = h(x)+3
extern let host_value(n: U32): U32
let after_host(n: U32): U32 = host_value(n)
let use_host(n: U32): U32 = after_host(n)+7
let discard(n: U32): U32 = do after_host(n) h(n) return n+1 end
let opaque(f: (U32): U32,x: U32): U32 = f(x)
let via(f: (U32): U32,x: U32): U32 = opaque(f,x)+3
let quotient(n: U32): U32 = 100/n
let guarded(n: U32): U32 = quotient(n)+5
return {functions={even,odd,nested_a,cycle_a,pair_a,set,get,null_a,mixed_a,walk,defer_a,
  helper_a,helper_b,use_host,discard,via,guarded,alias=even,module_a,via_callback,via_delayed,
  nested_self,known_self,mixed_choose,effect_choose,signed_zero,static_pc}}
]]

-- Snapshot reflected nodes/lists before lower.close. Contextual emission may build side tables and
-- new normalized functions, but it cannot change any field of an independently elaborated body.
local function closeAgain(artifact)
    local layouts = C.close(artifact.compilation)
    local saved, seen = {}, {}
    for _, instance in ipairs(layouts.order) do
        local visitor = {enter=function(node)
            if seen[node] then return false end
            seen[node] = true
            for _, field in ipairs((getmetatable(node) or {}).__fields or {}) do
                local row = {node=node, name=field.name, value=node[field.name]}
                if field.list and row.value then
                    row.items = {}
                    for i, item in ipairs(row.value) do row.items[i]=item end
                end
                saved[#saved+1]=row
            end
        end}
        for _, param in ipairs(instance.fn.params) do Walk.walk(param, visitor) end
        for _, stmt in ipairs(instance.fn.body) do Walk.walk(stmt, visitor) end
    end
    Lower.close(layouts)
    for _, row in ipairs(saved) do
        check(row.node[row.name] == row.value, "emission mutated a template field")
        if row.items then
            check(#row.value == #row.items, "emission resized a template list")
            for i, item in ipairs(row.items) do check(row.value[i] == item, "emission replaced a template list element") end
        end
    end
    check(Lower.unit(layouts) == artifact:unit(), "reclosing the same compilation is deterministic")
end

local directory = os.tmpname(); os.remove(directory)
assert(command("mkdir -p -- " .. q(directory)))
local CC = os.getenv("CC") or "cc"
local ok, err = xpcall(function()
    for _, budget in ipairs({0,256}) do
        local artifact = W.compile{source=program, residualInlineBudget=budget}
        closeAgain(artifact)
        check(artifact:unit() == W.compile{source=program,residualInlineBudget=budget}:unit(), "repeated compilation is deterministic")
        local names = {}
        for _, export in ipairs(artifact.compilation.functions) do names[export.name] = export.instance.target end
        local reports = {}
        for _, report in ipairs(artifact.layouts.contextual.reports) do
            reports[report.target] = report
            check(report.weight <= report.mandatory + budget, "per-unit expansion bound")
        end
        for _, name in ipairs({"even","odd","nested_a","cycle_a","pair_a","null_a","module_a"}) do
            check(reports[names[name]].jumps > 0, "missing tail component for " .. name)
        end
        check(reports[names.walk].jumps == 0 and reports[names.defer_a].jumps == 0, "borrow/cleanup owners cannot reuse activations")
        if budget > 0 then
            check(reports[names.helper_a].calls == 0 and reports[names.helper_b].calls == 0, "small helpers expand without calls")
            check(reports[names.use_host].expansions > 0 and reports[names.via].expansions > 0, "exercise foreign and opaque local returns")
        end
        local tuple = artifact.layouts.signatures[names.pair_a].results.name
        local view = artifact.layouts.signatures[names.via].params[1].type
        local viewName = artifact.layouts:cType(view)
        local main = [[
#include <assert.h>
#include <signal.h>
#include <stdlib.h>
#include <math.h>
uint32_t host_value(uint32_t n) { return n*2; }
static uint32_t remaining;
bool host_more(void) { if (remaining==0) return false; --remaining; return true; }
static uint32_t plus(const void *environment, uint32_t x) { (void)environment; return x+1; }
static void aborted(int sig) { (void)sig; _Exit(86); }
int main(int argc, char **argv) {
  (void)argv;
  if (argc>1) { signal(SIGABRT,aborted); (void)wordlet_guarded(0); return 1; }
  wordlet_init();
  assert(wordlet_get()==0); /* Building delayed must not execute bump. */
  wordlet_set(41); assert(wordlet_via_5Fcallback()==41);
  assert(wordlet_via_5Fdelayed()==42); assert(wordlet_get()==42);
  wordlet_set(5000000); wordlet_module_5Fa(); assert(wordlet_get()==0);
  assert(wordlet_nested_5Fself(5000000,0)==7500000);
  assert(wordlet_known_5Fself(5000000,0)==5000000);
  assert(wordlet_static_5Fpc(5000000,7)==15000010);
  assert(!signbit(wordlet_signed_5Fzero(true)));
  assert(signbit(wordlet_signed_5Fzero(false)));
  TUPLE mixed = wordlet_mixed_5Fchoose(false,2);
  assert(mixed.f_1==12 && mixed.f_2==13);
  mixed = wordlet_mixed_5Fchoose(true,2);
  assert(mixed.f_1==2 && mixed.f_2==3);
  wordlet_set(0); mixed=wordlet_effect_5Fchoose(true);
  assert(mixed.f_1==2 && mixed.f_2==3 && wordlet_get()==2);
  wordlet_set(0); mixed=wordlet_effect_5Fchoose(false);
  assert(mixed.f_1==3 && mixed.f_2==4 && wordlet_get()==3);
  assert(wordlet_even(5000000));
  assert(wordlet_odd(5000001));
  assert(wordlet_alias(5000000));
  assert(wordlet_nested_5Fa(5000000));
  assert(wordlet_cycle_5Fa(5000000,13,27)==1327);
  assert(wordlet_cycle_5Fa(5000001,13,27)==2713);
  TUPLE pair = wordlet_pair_5Fa(5000001,13,27);
  assert(pair.f_1==27 && pair.f_2==13);
  remaining=5000000; wordlet_null_5Fa(); assert(remaining==0);
  for(uint32_t n=0;n<40;++n) {
    uint32_t expected=0;
    for(uint32_t i=n;i>0;i=(i>1?i-2:0)) expected+=i;
    assert(wordlet_mixed_5Fa(n)==expected);
    assert(wordlet_walk(n)==n*(n+1)/2);
    wordlet_set(0); assert(wordlet_defer_5Fa(n)==0); assert(wordlet_get()==n*(n+1)/2);
  }
  for(uint32_t x=0;x<20;++x) for(uint32_t y=0;y<20;++y)
    assert(wordlet_helper_5Fa(x,y)==(x+y)*6+10);
  assert(wordlet_helper_5Fb(17)==110);
  assert(wordlet_use_5Fhost(5)==17);
  assert(wordlet_discard(5)==6);
  VIEW callback={plus,NULL}; assert(wordlet_via(callback,12)==16);
  assert(wordlet_guarded(4)==30);
  return 0;
}
]]
        main = main:gsub("TUPLE",tuple):gsub("VIEW",viewName)
        local path, exe = directory.."/tail.c", directory.."/tail"
        write(path,artifact:unit() .. main .. "\n")
        for _, optimization in ipairs({"0","2","3"}) do
            local flags = " -std=c11 -Wall -Wextra -Werror -pedantic -O" .. optimization
                .. " -fno-inline -fno-optimize-sibling-calls -DWORDLET_NO_FORCED_INLINE "
            check(command("timeout --kill-after=2s 30s " .. CC .. flags .. q(path) .. " -o " .. q(exe)
                .. " 2> " .. q(directory.."/errors")), "tail C compilation failed: " .. read(directory.."/errors"))
            check(command("timeout --kill-after=2s 10s sh -c " .. q("ulimit -s 256; ulimit -c 0; exec " .. q(exe))), "tail execution failed")
            local status = os.execute("timeout --kill-after=2s 10s " .. q(exe) .. " abort")
            check(status == 86*256, "expanded guard must abort, not return or segfault")
        end
        -- Also compile with the normal host attributes: mixed recursive roots must not force-inline.
        check(command("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 " .. q(path)
            .. " -o " .. q(exe) .. " 2> " .. q(directory.."/errors")), "recursive linkage failed: " .. read(directory.."/errors"))
    end
    -- Both facade paths reach contextual closure, and separately compiled headers preserve ABI.
    write(directory.."/helper.let", [[
let even(n: U32): Bool = if n==0 then true else odd(n-1)
let odd(n: U32): Bool = if n==0 then false else even(n-1)
return {functions={even}}
]])
    write(directory.."/entry.let", "use helper\nlet run(n: U32): Bool=helper.even(n)\nreturn {functions={run}}\n")
    local imported = W.compile_file(directory.."/entry.let", {residualInlineBudget=256,inline=false})
    check(imported.layouts.contextual.reports[1].jumps>0 and imported.layouts.contextual.reports[1].calls==0,
        "file compilation expands an imported tail component")
    write(directory.."/api.h",imported:header("api"))
    write(directory.."/api.c",imported:source("api.h"))
    write(directory.."/main.c", '#include "api.h"\n#include <assert.h>\nint main(void) { assert(wordlet_run(5000000)); return 0; }\n')
    check(command("timeout --kill-after=2s 30s "..CC.." -std=c11 -Wall -Wextra -Werror -O0 -fno-inline -fno-optimize-sibling-calls "
        ..q(directory.."/api.c").." "..q(directory.."/main.c").." -o "..q(directory.."/imported")), "separate header/source compilation")
    check(command("timeout 10s sh -c "..q("ulimit -s 256; exec "..q(directory.."/imported"))), "imported deep tail execution")
    for _, value in ipairs({-1,0.5,math.huge,"yes"}) do
        local success, failure = pcall(W.compile,{source="let f(): U32=1 return {functions={f}}", residualInlineBudget=value})
        check(not success and failure.code == "compile-option", "invalid expansion credit rejected")
    end
    local success, failure = pcall(W.compile,{source="let f(): U32=1 return {functions={f}}", limits={emittedNodes=0}})
    check(not success and failure.code == "c-size", "mandatory code respects hard output limit")
    local chain={"let d0(x: U32): U32=x+1"}
    for i=1,18 do chain[#chain+1]=("let d%d(x: U32): U32=d%d(x)+d%d(x+1)"):format(i,i-1,i-1) end
    chain[#chain+1]="return {functions={d18}}"
    local artifact=W.compile{source=table.concat(chain,"\n"),residualInlineBudget=64}
    for _, report in ipairs(artifact.layouts.contextual.reports) do
        check(report.weight<=report.mandatory+64,"repeated-helper expansion remains bounded")
    end
    check(#artifact.layouts.order<=19,"outline root discovery is finite")
end, debug.traceback)
command("rm -rf -- " .. q(directory))
if not ok then error(err,0) end
print(("PASS: contextual emission and tail components (%d checks)"):format(checks))
