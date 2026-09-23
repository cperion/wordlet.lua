-- Schema-driven traversal. The kernel reads the generated ASDL classes rather than a child list
-- kept in step by hand, so a field added to ast.asdl or ir.asdl is traversed at once. This suite
-- checks the kernel against the schemas and asserts the sums a visitor relies on are enumerable.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local A = require("wordlet.ast")
local S = require("wordlet.schema")
local Walk = require("wordlet.walk")
local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end

-- Every sum enumerates at least one variant, and every variant is a class with fields.
for _, ctx in ipairs({ A.ctx, S.ctx }) do
    local sums = Walk.sums(ctx)
    check(#sums > 0, "a context defines sums")
    for _, sum in ipairs(sums) do
        check(#sum.variants > 0, sum.name .. " has variants")
        for _, variant in ipairs(sum.variants) do
            local class = ctx.definitions[variant]
            check(class ~= nil and class.__fields ~= nil, variant .. " is a variant class")
        end
    end
end

-- `children` is exactly the semantic fields the class declares: the node-valued ones, with the
-- `span` attribute left out, and lists expanded by `nodeChildren`.
local span = A.c.Span("t.let", 1, 0, 3)
local reference = A.c.Reference(A.c.Name("f", span), span)
local apply = A.c.Apply(reference, A.List({ reference }), span)
local fields = Walk.children(apply)
local got = {}
for _, child in ipairs(fields) do got[child.name] = true end
check(got.callee and got.arguments, "the node-valued fields are children")
check(not got.span, "the span attribute is not a child")
check(#fields == 2 and #Walk.nodeChildren(apply) == 2, "a list field expands to its items")

-- The AST sums the analyses depend on are all present, so adding a sum is a visible change rather
-- than a silent one.
local names = {}
for _, sum in ipairs(Walk.sums(A.ctx)) do names[sum.name] = true end
for _, expected in ipairs({ "Ast.Expr", "Ast.Stmt", "Ast.Decl", "Ast.Body",
    "Ast.ResultSpec", "Ast.SchemaMember", "Ast.ExportItem" }) do
    check(names[expected], expected .. " is enumerated")
end

print("PASS: schema-driven traversal (" .. checks .. " checks)")
