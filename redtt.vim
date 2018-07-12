" vim-redtt syntax
" Language:     redtt
" Author:       Carlo Angiuli
" Last Change:  2018 July 3

" Move this file to ~/.vim/syntax/ and add the following line to your .vimrc:
"   au BufNewFile,BufRead *.red setf redtt

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword=a-z,A-Z,48-57,-,',/

syn sync minlines=50

syn match   redttParenErr ')'
syn match   redttBrackErr ']'

syn region  redttEncl transparent start="(" end=")" contains=ALLBUT,redttParenErr
syn region  redttEncl transparent start="\[" end="\]" contains=ALLBUT,redttBrackErr

syn match   redttHole '?\k*'

syn keyword redttKeyw V in with end bool nat ℕ S1 car cdr coe com cons hcom comp vproj
syn keyword redttKeyw restrict if nat-rec int-rec S1-rec lam call tt ff zero suc
syn keyword redttKeyw pos negsuc base loop pre kan U type then else

syn keyword redttDecl opaque let debug import

syn match   redttSymb '[#@`|^*×:,.▷=⇒→<>λ]\|->'

syn region  redttComm start=";" end="$"

hi def link redttParenErr Error
hi def link redttBrackErr Error
hi def link redttHole Special
hi def link redttKeyw Identifier
hi def link redttDecl Statement
hi def link redttSymb Identifier
hi def link redttComm Comment

let b:current_syntax = "redtt"
