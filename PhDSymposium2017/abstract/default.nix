with import <nixpkgs> {};

with callPackage ./support.nix {};

runCommand "phd-symposium-2017-abstract.pdf"
  {
    buildInputs = [ tex ];

    abstract = ./abstract.tex;
    class    = ./sig-alternate.cls;
    acm      = ./acm_proc_article-sp.cls;
    bibtex   = ../../Bibtex.bib;

    inherit data;
  }
  ''
    # Put LaTeX stuff in place
    cp -v "$abstract" ./abstract.tex
    cp -v "$class"    ./default.cls
    cp -v "$bibtex"   ./Bibtex.bib
    cp -v "$acm" ./acm_proc_article-sp.cls

    # Put supporting material in place
    ln -s "$data" ./data

    # Render
    export HOME="$PWD"

    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    bibtex abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract

    # Store resulting PDF
    cp abstract.pdf "$out"
  ''
