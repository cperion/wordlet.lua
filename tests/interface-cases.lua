-- Shared interpreter/C witnesses. Expectations are independent of either implementation.
return {
    name = "schema_interfaces",
    source = [==[
let counter = { n: u32, bump(): u32 = do n += 1 return n end }
let double = { n: u32, bump(): u32 = do n += 2 return n end }
let plain = { n: u32 }
let parent = {
    child: counter,
    twice(): u32 = do child.bump() return child.bump() end,
}
let shared = counter { n = 5 }
let shared_parent = parent { child = counter { n = 5 } }
let bump(c: counter): u32 = c.bump()
let through(r: ref(counter)): u32 = r.bump()
let make(x: u32): counter = double { n = x }
let inferred(x: u32) = counter { n = x }
let generic(t: type, c: t): u32 = c.bump()
let apply(f: (): u32): u32 = f()
let choose(b: bool): counter = if b then counter { n = 4 } else double { n = 5 }
let choose_same(b: bool) = if b then counter { n = 4 } else counter { n = 5 }
let choose_returns(b: bool) = do
    if b then return counter { n = 4 } end
    return counter { n = 5 }
end
let referenced(): ref(counter) = ref(shared)
let holder = { item: ref(counter) }
let stepper = { step: u32, n: u32, bump(): u32 = do n += step return n end }
let step_one = stepper { step = 1 }
let step_two = stepper { step = 2 }
let step_parent = { child: step_one }
let step_generic(t: type, c: t): u32 = c.bump()

let nested(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    p.child.bump()
    return p.twice() * 10 + p.child.n
end
let copied(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    let c = p.child
    c.bump()
    return c.n * 10 + p.child.n
end
let snapshot(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    let c = p.child
    p.child.bump()
    return c.n * 10 + p.child.n
end
let declared(x: u32): u32 = do
    let p = parent { child = double { n = x } }
    let first = p.child.bump()
    p.child = double { n = 10 }
    return first * 100 + p.child.bump()
end
let parameter(x: u32): u32 = do
    let c = double { n = x }
    return bump(c) * 10 + c.n
end
let result(x: u32): u32 = do let c = make(x) return c.bump() end
let inferred_result(x: u32): u32 = do let c = inferred(x) return c.bump() end
let annotated_alias(x: u32): u32 = do
    let c = double { n = x }
    let a: counter = c
    a.bump()
    c.bump()
    return c.n
end
let lambda_parameter(x: u32): u32 = (|c: counter| -> c.bump())(double { n = x })
let lambda_result(x: u32): u32 = do
    let f = |n: u32| -> counter { n = n }
    let c = f(x)
    return c.bump()
end
let specialization(x: u32): u32 =
    generic(counter, plain { n = x }) * 10 + generic(double, plain { n = x })
let joined(x: u32): u32 = do let c = choose(x == 0) return c.bump() end
let joined_same(x: u32): u32 = do let c = choose_same(x == 0) return c.bump() end
let returning_arms(x: u32): u32 = do let c = choose_returns(x == 0) return c.bump() end
let reference(x: u32): u32 = do shared.n = x return through(ref(shared)) end
let reference_result(x: u32): u32 = do shared.n = x return referenced().bump() end
let reference_field(x: u32): u32 = do
    shared.n = x
    let h = holder { item = ref(shared) }
    return h.item.bump() * 10 + shared.n
end
let module_child(x: u32): u32 = do
    shared_parent.child.n = x
    return shared_parent.child.bump() * 10 + shared_parent.child.n
end
let callback(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    let action = p.child.bump
    let before = p.child.n
    p.child.n += 10
    return apply(action) * 100 + before * 10 + p.child.n
end
let deferred(x: u32): u32 = do
    shared_parent.child.n = x
    defer shared_parent.child.bump()
    return shared_parent.child.n
end
let cleanup(x: u32): u32 = do let old = deferred(x) return old * 10 + shared_parent.child.n end
let configured(x: u32): u32 = do
    let p = step_parent { child = step_one { n = x } }
    return p.child.bump() * 10 + step_generic(step_two, step_two { n = x })
end
let array_element(x: u32): u32 = do
    let cells: array(counter, 2) = [double { n = x }, double { n = x + 1 }]
    cells[0].bump()
    return cells[0].n * 10 + cells[1].n
end
let array_dynamic(x: u32): u32 = do
    let cells: array(counter, 2) = [double { n = x }, double { n = x + 1 }]
    cells[x % 2].bump()
    return cells[0].n * 10 + cells[1].n
end
let parent_copy(p: parent): u32 = p.twice()
let deep_copy(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    return parent_copy(p) * 10 + p.child.n
end
let local_alias(x: u32): u32 = do
    let p = parent { child = counter { n = x } }
    let a = p
    a.child.bump()
    return p.child.n
end
return { functions = { nested, copied, snapshot, declared, parameter, result, inferred_result,
    annotated_alias, lambda_parameter, lambda_result, specialization, joined, joined_same,
    returning_arms, reference, reference_result, reference_field, module_child, callback,
    cleanup, configured, deep_copy, local_alias, array_element, array_dynamic } }
]==],
    entries = {
        { entry = "nested", arity = 1, inputs = {{0}, {3}}, expected = {33, 66} },
        { entry = "copied", arity = 1, inputs = {{0}, {3}}, expected = {10, 43} },
        { entry = "snapshot", arity = 1, inputs = {{0}, {3}}, expected = {1, 34} },
        { entry = "declared", arity = 1, inputs = {{0}, {3}}, expected = {111, 411} },
        { entry = "parameter", arity = 1, inputs = {{0}, {3}}, expected = {10, 43} },
        { entry = "result", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "inferred_result", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "annotated_alias", arity = 1, inputs = {{0}, {3}}, expected = {3, 6} },
        { entry = "lambda_parameter", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "lambda_result", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "specialization", arity = 1, inputs = {{0}, {3}}, expected = {12, 45} },
        { entry = "joined", arity = 1, inputs = {{0}, {3}}, expected = {5, 6} },
        { entry = "joined_same", arity = 1, inputs = {{0}, {3}}, expected = {5, 6} },
        { entry = "returning_arms", arity = 1, inputs = {{0}, {3}}, expected = {5, 6} },
        { entry = "reference", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "reference_result", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
        { entry = "reference_field", arity = 1, inputs = {{0}, {3}}, expected = {11, 44} },
        { entry = "module_child", arity = 1, inputs = {{0}, {3}}, expected = {11, 44} },
        { entry = "callback", arity = 1, inputs = {{0}, {3}}, expected = {1111, 1444} },
        { entry = "cleanup", arity = 1, inputs = {{0}, {3}}, expected = {1, 34} },
        { entry = "configured", arity = 1, inputs = {{0}, {3}}, expected = {12, 45} },
        { entry = "array_element", arity = 1, inputs = {{0}, {3}}, expected = {11, 44} },
        { entry = "array_dynamic", arity = 1, inputs = {{0}, {3}}, expected = {11, 35} },
        { entry = "deep_copy", arity = 1, inputs = {{0}, {3}}, expected = {20, 53} },
        { entry = "local_alias", arity = 1, inputs = {{0}, {3}}, expected = {1, 4} },
    },
}
