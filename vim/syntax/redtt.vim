" vim-redtt syntax
" Language:     redtt
" Author:       Carlo Angiuli
" Last Change:  2018 September 11

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword=a-z,A-Z,48-57,-,',/

syn sync minlines=50
syn sync maxlines=1000

syn match   redttParenErr ')'
syn match   redttBrackErr ']'

syn region  redttEncl transparent matchgroup=redttSymb start="(" end=")" contains=ALLBUT,redttParenErr
syn region  redttEncl transparent matchgroup=redttSymb start="\[" end="\]" contains=ALLBUT,redttBrackErr

syn match   redttHole '?\k*'

syn keyword redttKeyw V in with where end tick dim elim fst snd coe com pair
syn keyword redttKeyw hcom comp vproj vin lam next prev dfix fix call refl pre
syn keyword redttKeyw kan U type

syn keyword redttDecl let data debug normalize import quit opaque

syn match   redttSymb '[#@`|^*×:,.∙✓□▷=∂→λ𝕀]\|->'

syn region  redttComm start="\k\@1<!--" end="$"
syn region  redttBlockComm start="/-" end="-/" contains=redttBlockComm

hi def link redttParenErr Error
hi def link redttBrackErr Error
hi def link redttHole Special
hi def link redttKeyw Identifier
hi def link redttDecl Statement
hi def link redttSymb Identifier
hi def link redttComm Comment
hi def link redttBlockComm Comment

let b:current_syntax = "redtt"
