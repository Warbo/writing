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

# Get styles, if we haven't already
[[ -e "mathpartir.sty" ]] ||
wget "http://cristal.inria.fr/~remy/latex/mathpartir.sty"

[[ -e "mmm.sty" ]] ||
wget "http://www.ccs.neu.edu/course/csg264/latex/mmm.sty"

[[ -e "psfig.sty" ]] ||
wget "http://anorien.csc.warwick.ac.uk/mirrors/CTAN/graphics/psfig/psfig.sty"

run "$NAME"           &&
echo "RUNNING bibtex" &&
bibtex "$NAME"        &&
run "$NAME"           &&
run "$NAME"
