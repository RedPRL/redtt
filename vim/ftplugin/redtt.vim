" vim-redtt ftplugin
" Language:     redtt
" Author:       Carlo Angiuli
" Last Change:  2018 August 13

if (exists("b:did_ftplugin") || !has('job'))
  finish
endif

if (!exists('g:redtt_path'))
  let g:redtt_path = 'redtt'
endif

if (!exists('g:redtt_options'))
  let g:redtt_options = ''
endif

command! Redtt :call CheckBuffer()
nnoremap <buffer> <LocalLeader>l :call CheckBuffer()<CR>
nnoremap <buffer> <LocalLeader>p :call CheckBufferToCursor()<CR>
autocmd QuitPre <buffer> call s:CloseBuffer()

" Optional argument: the last line to send to redtt (default: all).
function! CheckBuffer(...)
  if (exists('s:job'))
    call job_stop(s:job, 'int')
  endif

  if (!bufexists('redtt') || (winbufnr(bufwinnr('redtt')) != bufnr('redtt')))
    belowright vsplit redtt
    call s:InitBuffer()
  else
    execute bufwinnr('redtt') . 'wincmd w'
  endif
  silent %d _
  wincmd p

  let s:job = job_start(g:redtt_path .
    \' from-stdin ' . bufname('%') .
    \' ' . g:redtt_options .
    \' --line-width ' . s:EditWidth(), {
    \'in_io': 'buffer', 'in_buf': bufnr('%'),
    \'in_bot': exists('a:1') ? a:1 : line('$'),
    \'out_io': 'buffer', 'out_name': 'redtt', 'out_msg': 0,
    \'err_io': 'buffer', 'err_name': 'redtt', 'err_msg': 0})
endfunction

function! CheckBufferToCursor()
  call CheckBuffer(line('.'))
endfunction

function! s:InitBuffer()
  set buftype=nofile
  set syntax=redtt
  set noswapfile
endfunction

function! s:EditWidth()
  execute bufwinnr('redtt') . 'wincmd w'

  let l:width = winwidth(winnr())
  if (has('linebreak') && (&number || &relativenumber))
    let l:width -= &numberwidth
  endif
  if (has('folding'))
    let l:width -= &foldcolumn
  endif
  if (has('signs'))
    redir => l:signs
    silent execute 'sign place buffer=' . bufnr('%')
    redir END
    if (&signcolumn == "yes" || len(split(l:signs, "\n")) > 2)
      let l:width -= 2
    endif
  endif

  wincmd p
  return l:width
endfunction

function! s:CloseBuffer()
  cclose
  if (bufexists('redtt') && !getbufvar('redtt', '&modified'))
    bdelete redtt
  endif
endfunction

let b:did_ftplugin = 1

digraph II 120128
digraph !- 8866
