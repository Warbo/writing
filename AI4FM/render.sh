#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash

function renderLatex {
    latex    article &&
    bibtex   article &&
    latex    article &&
    pdflatex article
}

function clean {
    { rm article.aux;
      rm article.blg;
      rm article.log;
      rm article.pdf;
      rm article.bbl;
      rm article.dvi;
      rm article.out; } 2> /dev/null
    return 0
}

function go {
    renderLatex
}

# Run once (default) or forever (if given any argument)

go

while [ "x$1" = "xloop" ]
do
    sleep 2
    go
done
