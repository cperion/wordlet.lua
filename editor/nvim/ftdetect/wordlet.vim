" Wordlet sources use the `.let` extension (syntax.md §11).
augroup wordlet_filetype
  autocmd!
  autocmd BufRead,BufNewFile *.let setfiletype wordlet
augroup END
