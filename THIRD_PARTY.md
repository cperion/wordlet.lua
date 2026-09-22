# Dependency provenance

This file records origins so the directory remains intelligible after extraction. None of these
original paths are runtime/build dependencies of the extracted project.

## ASDL and terralist

Copied from the root `asdl.lua` and `terralist.lua` in the let repository at commit
`0bcbaa7c4e75b2336156b55167179821ac6d2b4e` (repository origin: https://github.com/cperion/let).
Their original SHA-256 values were:

```
asdl.lua     4ff2be1fb8746d505e85b80d8d40d3351e8518b9285ea18654efe9b9e8dfb62e
terralist.lua b42fddbdb4dcc3a4648109ca90ec5977520ae372dcad6766932f8a80bf0badc3
```

Local changes:

- ASDL requires `vendor.terralist` rather than a root module named terralist.
- Both files return their module value instead of installing a hardcoded package.loaded name.
- terralist's duplicate `~=` selector was corrected: the equality entry is now `==`, leaving `~=`
  as inequality. The bootstrap tests cover both.

The original files were verified byte-for-byte against Terra commit
`97e179138ce69ff61f3cabff55b43ca08e4500d3`:

- https://github.com/terralang/terra/blob/97e179138ce69ff61f3cabff55b43ca08e4500d3/src/asdl.lua
- https://github.com/terralang/terra/blob/97e179138ce69ff61f3cabff55b43ca08e4500d3/src/terralist.lua

Terra's MIT license carries `Copyright (C) 2013 Stanford University.` The full upstream notice is
preserved in `vendor/LICENSE`; upstream path:
https://github.com/terralang/terra/blob/97e179138ce69ff61f3cabff55b43ca08e4500d3/release/share/terra/LICENSE.txt
(The upstream root LICENSE.txt points to that file.)

This project also uses the MIT license, in `LICENSE`. Keep the notices with redistributed source and
substantial copies. The default bundle manifest embeds both notices in generated single-file output.

## Bundler

`tools/bundle.lua` is a standalone manifest-driven implementation. It carries over the useful
single-file module-factory/CLI pattern, not the old compiler's module graph or require scanner.
For historical identification, the former `new/bundle.lua` at the same commit had SHA-256
`58342ebffa50ff5167a05a07f2c201df567ed59188e6450621aafb1b80d5025f`.
No old compiler module is required or packaged.

## Host tools

LuaJIT 2.1 is an installed tool, not vendored here. POSIX shell utilities and timeout are used by the
builder/test harness as documented in README.md. A future C11 compiler is also an external tool.
No tool binary or claim about its redistribution rights is included in this seed.
