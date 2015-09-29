" Syntax highlighting for the .netdecomp file format.
"
"To use automatically, add the following line to .vimrc
"
"  autocmd BufNewFile,BufRead *.netdecomp set filetype=netdecomp
"

if exists("b:current_syntax")
  finish
endif

syn keyword componentCmd NET PLACES LBOUNDS RBOUNDS TRANS WIRING IMPORT
syn match   keyword "\<bind\>\|\<in\>\|\<fold\>"
syn match   operator "\.\|\*\|;\|\\\|="
syn match   comment skipwhite "--.*"

" Highlighting Settings
" ====================

hi def link componentCmd Statement
hi def link operator     Operator
hi def link keyword      Keyword
hi def link comment      Comment
