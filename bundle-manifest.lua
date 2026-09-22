-- Trusted build configuration. Paths are relative to this file.
return {
    entry = "wordlet",
    cli = "wordlet.cli",
    output = "dist/wordlet.lua",
    licenses = {"LICENSE", "vendor/LICENSE"},
    modules = {
        ["wordlet"] = "wordlet/init.lua",
        ["wordlet.cli"] = "wordlet/cli.lua",
        ["wordlet.diag"] = "wordlet/diag.lua",
        ["wordlet.docs.syntax"] = "wordlet/docs/syntax.lua", -- the language reference, embedded
        ["wordlet.lex"] = "wordlet/lex.lua",
        ["wordlet.ast"] = "wordlet/ast.lua",
        ["wordlet.parse"] = "wordlet/parse.lua",
        ["wordlet.schema"] = "wordlet/schema.lua",
        ["wordlet.schema.ast"] = "wordlet/schema/ast.lua",
        ["wordlet.schema.ir"] = "wordlet/schema/ir.lua",
        ["wordlet.value"] = "wordlet/value.lua",
        ["wordlet.ir"] = "wordlet/ir.lua",
        ["wordlet.resolve"] = "wordlet/resolve.lua",
        ["wordlet.eval"] = "wordlet/eval.lua",
        ["wordlet.check"] = "wordlet/check.lua",
        ["wordlet.cabi"] = "wordlet/cabi.lua",
        ["wordlet.lower"] = "wordlet/lower.lua",
        ["wordlet.jit"] = "wordlet/jit.lua", -- the LuaJIT FFI front end (uses the host C compiler)
        ["wordletkit.u32"] = "wordletkit/u32.lua",
        ["wordletkit.u64"] = "wordletkit/u64.lua",
        ["vendor.asdl"] = "vendor/asdl.lua",
        ["vendor.terralist"] = "vendor/terralist.lua",
    },
    external = {"bit", "ffi"}, -- LuaJIT built-ins: bit for wordletkit.u32, ffi for the jit loader
}
