#! /usr/bin/env nix-shell
#! nix-shell -i bash -p ditaa bash
pdflatex --shell-escape summer
bibtex summer
pdflatex --shell-escape summer
