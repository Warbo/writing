#! /usr/bin/env nix-shell
#! nix-shell -i bash -p ditaa bash

NAME=report

run() {
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape "$1"
}

for EXT in aux bbl blg log out pdf
do
    rm -f "${NAME}.${EXT}"
done

latex "$NAME" && bibtex "$NAME" && latex "$NAME" && pdflatex "$NAME"
