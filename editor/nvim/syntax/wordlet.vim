" Vim syntax file
" Language:     Wordlet (the new iteration of Let)
" Maintainer:   the Wordlet project
" Last Change:  2025
"
" Wordlet's core is the *word*: a word with ordered or keyed requirements, an
" optional result contract and an optional terminal. A signature is a word with
" no implementation; a schema is a word with keyed requirements and an intrinsic
" constructor; a method is a word with an implicitly bound receiver. Types are
" ordinary words too, and a type expression is an expression.
"
" The full mapping from Wordlet's roles onto Vim's highlight groups, with the
" reason for each choice and for every group deliberately left unused, is in
" editor/README.md. Two invariants govern the rules below:
"
"   1. ROLE COMES FROM POSITION, NEVER SPELLING.
"      syntax.md §1: "capitalization never distinguishes a type from a value or
"      a signature from a lambda." A name is classified by the keyword that
"      introduces it (`let`), by the punctuation it follows (`.` `:`), or by
"      the token it precedes (`(`).
"
"   2. NEVER LIE WHERE THE RESOLVER IS NEEDED.
"      A regex cannot see a receiver's schema, so `r.value` (field), `r.draw()`
"      (method) and `Opt.some()` (alternative) are one group, and
"      `Point { ... }` is indistinguishable from `s { ... }`. Those are left
"      neutral for a language server's semantic tokens. This file never guesses.
"
" Mechanism. Vim tries a syntax item only where scanning resumes, so a rule
" cannot begin with `let`, `:` or `.` after those are already matched. The
" positional rules therefore use `nextgroup` on the introducing keyword or
" delimiter, as rust.vim and go.vim do. Vim keeps the LAST item that matches at
" a column, so plain delimiters and keywords come first and the refining
" `nextgroup` rules come later.
"
" Set   let g:wordlet_highlight_heuristics = 0
" to keep only the rules that cannot be wrong (keywords, operators, literals,
" comments, imports) and leave every other name at the default Identifier.

if exists("b:current_syntax")
  finish
endif

let s:cpo_save = &cpo
set cpo&vim

syn case match
syn sync minlines=200

let s:heuristics = get(g:, "wordlet_highlight_heuristics", 1)

" Names reached through `nextgroup`. `contained` means they only fire where a
" keyword or delimiter sends the scanner to them, never on their own. The order
" matters: when a `nextgroup` list has two groups that both match, Vim keeps the
" one defined LAST, so the word form is defined after the plain binder it refines.
syn match wordletBinding  "\<[A-Za-z_]\w*" contained
syn match wordletWordDef  "\<[A-Za-z_]\w*\ze\s*(" contained
syn match wordletTypeName "\<[A-Za-z_]\w*" contained
syn match wordletMember   "\<[A-Za-z_]\w*" contained
syn match wordletSection  "\%(types\|functions\|results\)\ze[ \t]*=" contained

" Predefined words -------------------------------------------------------------
" Bindings the language provides, not user types. The constructors are `Special`
" so they read differently from the type names a program declares, and because a
" constructor is a word the program applies: OneOf({...}), Array(T, N), Ref(x).
syn keyword wordletType        U8 U16 U32 I32 U64 I64 F64 Bool Unit Type
syn keyword wordletConstructor String OneOf Ref Array Slice Ptr Null

" Reserved words, each by role -------------------------------------------------
" `extern let name(...)`: after `extern` the `let` keyword does the nextgroup.
syn keyword wordletStorage     extern
if s:heuristics
  syn keyword wordletKeyword let nextgroup=wordletWordDef,wordletBinding skipwhite skipnl skipempty
else
  syn keyword wordletKeyword let
endif
syn keyword wordletStatement   do end return defer
syn keyword wordletConditional if then else
syn keyword wordletOperator    and or not
syn keyword wordletBoolean     true false

" Operators and punctuation ----------------------------------------------------
" Declared after the words: when two items match at one column Vim keeps the
" LAST, so literals and names declared below win over a bare `-`, `.`, `[`.
syn match wordletOperator "[+*/%^<>=~&|-]"
syn match wordletOperator "<<=\|>>=\|::\|->\|!=\|==\|<=\|>=\|<<\|>>"
syn match wordletOperator "\\+=\\|-=\\|\\*=\\|/=\\|%=\\|\\^=\\|&=\\||=\\|[~]="
syn match wordletDelimiter "[(){}\[\],;:.]"

" Contextual roles (heuristic) -------------------------------------------------
" `nextgroup` on the introducing token classifies the following name: ':' opens a
" type, '.' opens a member, '{' or ',' opens a config section, and 'let' opens a
" binder. Declared after the plain delimiters so these win at the same column.
if s:heuristics
  syn match wordletDelimiter ":" nextgroup=wordletType,wordletConstructor,wordletTypeName skipwhite skipnl skipempty
  syn match wordletDelimiter "\." nextgroup=wordletMember skipwhite skipnl skipempty
  syn match wordletDelimiter "{" nextgroup=wordletSection skipwhite skipnl skipempty
  syn match wordletDelimiter "," nextgroup=wordletSection skipwhite skipnl skipempty

  " A keyed requirement: a parameter or schema field before its ':'.
  syn match wordletKey "\<[A-Za-z_]\w*\ze\s*:"

  " A word applied to arguments: a call or a method definition. The predefined
  " type constructors are keywords and win at the same column, so Array(, Ref(
  " and OneOf( stay constructors.
  syn match wordletWord "\<[A-Za-z_]\w*\ze\s*("
endif

" Literals ---------------------------------------------------------------------
" Long strings: raw, leveled, at least one `=` (`[[` is an array, not a string).
syn region wordletString
      \ matchgroup=wordletStringDelimiter
      \ start="\[=\z(=*\)\["
      \ end="\]=\z1\]"
      \ keepend
      \ contains=@Spell
" `"..."` is a byte string; `'x'` is one byte, a numeric literal.
syn match  wordletEscape contained '\\[nrt0"'']'
syn match  wordletEscape contained '\\x[0-9A-Fa-f]\{2\}'
syn region wordletString
      \ matchgroup=wordletStringDelimiter
      \ start=+"+
      \ end=+"+
      \ skip=+\\\\\|\\"+
      \ oneline
      \ contains=wordletEscape,@Spell
syn region wordletByte
      \ matchgroup=wordletStringDelimiter
      \ start=+'+
      \ end=+'+
      \ skip=+\\\\\|\\'+
      \ oneline
      \ contains=wordletEscape,@Spell
" The integer precedes the float forms so a longer literal wins at one column.
syn match wordletNumber "\<\d\(_\?\d\)*\>"
syn match wordletFloat  "\<\d\(_\?\d\)*\.\d\(_\?\d\)*\%([eE][-+]\?\d\(_\?\d\)*\)\?\>"
syn match wordletFloat  "\<\d\(_\?\d\)*[eE][-+]\?\d\(_\?\d\)*\>"
syn match wordletNumber "\<0[xX]\x\(_\?\x\)*\>"
syn match wordletNumber "\<0[bB][01]\(_\?[01]\)*\>"

" Module import ----------------------------------------------------------------
" `use util.helper`: the dotted path is an import, like Vim's Include.
syn match wordletInclude "\<use\s\+[A-Za-z_]\w*\%(\.[A-Za-z_]\w*\)*"

" Comments ---------------------------------------------------------------------
" Declared last so `--` wins over the `-` operator. `--` runs to end of line;
" `--` immediately followed by a long bracket is a block comment at any level.
syn match  wordletComment "--.*$" contains=wordletTodo,@Spell
syn region wordletComment
      \ start="--\[\z(=*\)\["
      \ end="\]\z1\]"
      \ keepend
      \ contains=wordletTodo,@Spell
syn keyword wordletTodo contained TODO FIXME XXX NOTE

" Highlight links --------------------------------------------------------------
hi def link wordletKeyword         Keyword
hi def link wordletStorage         StorageClass
hi def link wordletStatement       Statement
hi def link wordletConditional     Conditional
hi def link wordletOperator        Operator
hi def link wordletBoolean         Boolean
hi def link wordletType            Type
hi def link wordletConstructor     Special
hi def link wordletTypeName        Type
hi def link wordletWord            Function
hi def link wordletWordDef         Function
hi def link wordletBinding         Identifier
hi def link wordletKey             Identifier
hi def link wordletMember          Identifier
hi def link wordletSection         Identifier
hi def link wordletInclude         Include
hi def link wordletDelimiter       Delimiter
hi def link wordletNumber          Number
hi def link wordletFloat           Float
hi def link wordletString          String
hi def link wordletStringDelimiter Delimiter
hi def link wordletByte            Character
hi def link wordletEscape          SpecialChar
hi def link wordletComment         Comment
hi def link wordletTodo            Todo

let b:current_syntax = "wordlet"

let &cpo = s:cpo_save
unlet s:cpo_save
