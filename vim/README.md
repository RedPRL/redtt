# redtt.vim

This vim plugin requires Vim 8 (released September 2016).

## Use

While editing a .red file, run `:Redtt` or `<LocalLeader>l` (`l` for `load`) in
the command (normal) mode to check the current buffer and display the output in
a separate buffer. Run `<LocalLeader>p` (`p` for `partial`) to check the current
buffer, ignoring lines below the cursor's current position.

## Setup

This plugin is compatible with Vim 8's package system. You can (re)install it by
running the following shell command from the current directory:

    chmod +x install.sh
    ./install.sh

If the `redtt` binary is not in your `PATH`, add the following line to your
`.vimrc`:

    let g:redtt_path = '/path/to/the-redtt-binary'
