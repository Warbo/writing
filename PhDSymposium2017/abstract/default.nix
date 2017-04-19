with import <nixpkgs> {};

with rec {
  tex = callPackage ../tex.nix {};
};

runCommand "phd-symposium-2017-abstract.pdf"
  {
    buildInputs = [ tex ];

    abstract = ./abstract.tex;
    class    = ./sig-alternate.cls;
    acm      = ./acm_proc_article-sp.cls;
    bibtex   = ../../Bibtex.bib;
  }
  ''
    cp -v "$abstract" ./abstract.tex
    cp -v "$class"    ./default.cls
    cp -v "$bibtex"   ./Bibtex.bib
    cp -v "$acm" ./acm_proc_article-sp.cls

    export HOME="$PWD"

    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    bibtex abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract

    cp abstract.pdf "$out"
  ''
