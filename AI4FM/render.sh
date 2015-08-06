#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash -p md2pdf

function renderMd {
    ARGS="--filter pandoc-citeproc" md2pdf
}

function mdToLatex {
    pandoc -s --filter pandoc-citeproc -o abstract.tex abstract.md
}

function renderLatex {
    latex abstract
    bibtex abstract
    latex abstract
    pdflatex abstract
}

function go {
    renderLatex
}

# Run once (default) or forever (if given any argument)

go

if [ "x$1" = "xloop" ]
then
    while true
    do
        sleep 2
        go
    done
fi
