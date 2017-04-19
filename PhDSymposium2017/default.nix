with import <nixpkgs> {};

with rec {
  tex = texlive.combine {
    inherit (texlive)
      scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
      frankenstein csquotes helvetic paralist;
  };
};

runCommand "phd-symposium-2017"
  {
    buildInputs = [ ditaa ghostscript haskellPackages.pandoc-citeproc
                    imagemagick pandoc panpipe panhandle tex ];

    # Required for Haskell and Perl to not barf at unicode
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

    abstract = ./abstract.tex;
    class    = ./sig-alternate.cls;
    acm      = ./acm_proc_article-sp.cls;
    bibtex   = ../Bibtex.bib;
    slides   = ./slides.md;
  }
  ''
    mkdir "$out"

    cp -v "$abstract" ./abstract.tex
    cp -v "$class"    ./default.cls
    cp -v "$bibtex"   ./Bibtex.bib
    cp -v "$acm" ./acm_proc_article-sp.cls

    export HOME="$PWD"

    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    bibtex abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract

    cp abstract.pdf "$out/abstract.pdf"

    pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
                    --filter panpipe --filter panhandle \
                    -o "$out/slides.html" "$slides"

    cp "$slides"   "$out/slides.html"
  ''
