#! /usr/bin/env nix-shell
#! nix-shell -i bash -p ditaa bash

NAME=report

run() {
    echo "RUNNING pdflatex"
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape "$1"
}

for EXT in aux bbl blg dvi log out pdf
do
    rm -f "${NAME}.${EXT}"
done

run "$NAME"           &&
echo "RUNNING bibtex" &&
bibtex "$NAME"        &&
run "$NAME"           &&
run "$NAME"
