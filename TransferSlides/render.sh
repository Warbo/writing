#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash pandoc haskellPackages.pandoc-citeproc ditaa

pandoc -w dzslides              \
       --standalone             \
       --self-contained         \
       --mathml                 \
       -o slides.html           \
       --filter=pandoc-citeproc \
       --filter=panpipe         \
       --filter=panhandle       \
       slides.md
