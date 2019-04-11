with { inherit (import ../resources) bibtex nixpkgs styles; };
with nixpkgs;
with {
  cmd = ''
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report
  '';
};

runCommand "ml4hs-tech-report"
  {
    inherit bibtex;
    src    = ./report.tex;
    styles = attrsToDirs' "styles" {
      inherit (styles) "mmm.sty" "psfig.sty" "mathpartir.sty";
    };


    buildInputs = [ (texlive.combine {
                      inherit (texlive) collection-latexrecommended
                                        algorithmicx algorithms paralist
                                        listings csquotes etoolbox epsf
                                        tikz-qtree titlesec;
                    }) ];
  }
  ''
    mkdir src
    cd    src

    cp "$styles"/*.sty .
    cp "$src"          report.tex
    cp "$bibtex"       Bibtex.bib

    ${cmd}

    echo "RUNNING bibtex"
    bibtex report

    ${cmd}
    ${cmd}

    cp report.pdf "$out"
  ''
