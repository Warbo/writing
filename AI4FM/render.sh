#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash -p md2pdf

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
    renderLatex && clean
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
