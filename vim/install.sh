#!/bin/bash

DEST=~/.vim/pack/redprl-org/start ;
[ -d $DEST/vim-redtt ] && rm -r $DEST/vim-redtt ;
mkdir -p $DEST && cp -r . $DEST/vim-redtt
