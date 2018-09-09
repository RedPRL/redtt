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

syn keyword redttKeyw boundary data intro where in with end elim
syn keyword redttKeyw V fst snd coe com pair hcom comp vproj
syn keyword redttKeyw refl restrict if lam call
syn keyword redttKeyw pre kan U type then else
syn keyword redttKeyw open shut tick dim prev next dfix fix


syn keyword redttDecl opaque let debug normalize import quit

syn match   redttSymb '[#@`|\[\]^*×:,.∙✓□▷=∂→()λ]\|->'

syn region  redttComm start=";" end="$"

hi def link redttParenErr Error
hi def link redttBrackErr Error
hi def link redttHole Special
hi def link redttKeyw Identifier
hi def link redttDecl Statement
hi def link redttSymb Identifier
hi def link redttComm Comment

let b:current_syntax = "redtt"
