#! /usr/bin/env nix-shell
#! nix-shell -i bash -p haskellPackages.pandoc-citeproc panpipe panhandle ditaa
pandoc -w dzslides --standalone --self-contained --mathml -o slides.html --filter=pandoc-citeproc --filter=panpipe --filter=panhandle slides.md
