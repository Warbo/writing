#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash -p md2pdf

function renderMd {
    ARGS="--filter pandoc-citeproc" md2pdf
}

function mdToLatex {
    pandoc -s --filter pandoc-citeproc -o article.tex article.md
}

function renderLatex {
    latex    article &&
    bibtex   article &&
    latex    article &&
    pdflatex article
}

function clean {
    rm article.aux
    rm article.blg
    rm article.log
    rm article.pdf
    rm article.bbl
    rm article.dvi
    rm article.out
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
