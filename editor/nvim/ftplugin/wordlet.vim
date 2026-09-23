" Filetype settings for Wordlet.
"
" `_` is part of an identifier, so it must be a keyword character for word
" motions and completion to agree with the language. Comments are `--` to end
" of line and `--[=[ ... ]=]` at any level.

if exists("b:did_ftplugin")
  finish
endif
let b:did_ftplugin = 1

setlocal iskeyword+=_
setlocal commentstring=--\ %s
setlocal comments=:--
setlocal suffixesadd=.let

let b:undo_ftplugin = "setlocal iskeyword< commentstring< comments< suffixesadd<"
