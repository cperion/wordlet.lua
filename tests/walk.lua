-- Schema-driven traversal. The kernel reads the generated ASDL classes rather than a child list
-- kept in step by hand, so a field added to ast.asdl or ir.asdl is traversed at once.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local A = require("wordlet.ast")
local S = require("wordlet.schema")
local Walk = require("wordlet.walk")
local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end

-- `children` is exactly the node-valued fields the class declares: the `span` attribute is left
-- out, and `nodeChildren` expands a list field.
local span = A.c.Span("t.let", 1, 0, 3)
local reference = A.c.Reference(A.c.Name("f", span), span)
local apply = A.c.Apply(reference, A.List({ reference }), span)
local fields = Walk.children(apply)
local got = {}
for _, child in ipairs(fields) do got[child.name] = true end
check(got.callee and got.arguments, "the node-valued fields are children")
check(not got.span, "the span attribute is not a child")
check(#fields == 2 and #Walk.nodeChildren(apply) == 2, "a list field expands to its items")

-- Both schema contexts enumerate their sums, so a visitor can rely on the schema, not a table.
check(#Walk.sums(A.ctx) > 0 and #Walk.sums(S.ctx) > 0, "both schemas enumerate their sums")

print("PASS: schema-driven traversal (" .. checks .. " checks)")
