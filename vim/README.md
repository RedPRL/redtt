# redtt.vim

This vim plugin requires Vim 8 (released September 2016).

## Use

While editing a .red file, run `:Redtt` or `<LocalLeader>l` (`l` for `load`) in
the command (normal) mode to check the current buffer and display the output in
a separate buffer.

If there are any syntax errors, the cursor will jump to the first one.

## Setup

Copy (or symlink) this directory to `~/.vim/pack/foo/start/vim-redtt`. (The
names `foo` and `vim-redtt` don't matter.)

If `redtt` is not in your `PATH`, add the following line to your `.vimrc`:

    let g:redtt_path = '/path/to/redtt'

If you want to recheck the current buffer with another key combination, add the
following line to your `.vimrc`, replacing `<F5>` as appropriate:

    au FileType redtt nnoremap <F5> :Redtt<CR>
