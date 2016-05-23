#!/bin/sh
nix-shell --command './pandoc.sh'
          #-p pandoc \
          #-p haskellPackages.pandoc-citeproc \
          #-p panpipe \
          #-p panhandle \
