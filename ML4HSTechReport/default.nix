with rec {
  inherit (import ../resources) bibtex nixpkgs styles;
  inherit (nixpkgs.repo1609.configless) fetchurl runCommand texlive;
};

runCommand "ml4hs-tech-report"
  {
    inherit bibtex;
    src    = ./.;
    styles = [ styles."mmm.sty" styles."psfig.sty" styles."mathpartir.sty" ];
    cmd    = ''
      pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report
    '';

    buildInputs = [ (texlive.combine {
                      inherit (texlive) collection-latexrecommended
                                        algorithmicx algorithms paralist
                                        listings csquotes etoolbox epsf
                                        tikz-qtree titlesec;
                    }) ];
  }
  ''
    source $stdenv/setup

    cp -r "$src" ./src
    chmod +w -R ./src
    cd ./src

    for S in $styles
    do
      NAME=$(basename "$S" | sed -e 's/.*-//g')
      cp "$S" ./"$NAME"
    done

    cp "$bibtex" ./Bibtex.bib

    $cmd

    echo "RUNNING bibtex"
    bibtex report

    $cmd
    $cmd

    cp report.pdf "$out"
  ''
