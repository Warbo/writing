with {
  inherit (import <nixpkgs> {}) fetchurl latestGit stdenv texlive;

  bibtex     = ../Bibtex.bib;
  haskell-te = null;#latestGit { url = http://chriswarbo.net/git/haskell-te.git; };
};

stdenv.mkDerivation {
  inherit bibtex;
  name = "ml4hs-tech-report";
  src  = ./.;

  styles = [
    ../TransferReport/mmm.sty
    ../TransferReport/psfig.sty
    ../TransferReport/mathpartir.sty
  ];

  cmd = "pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report";

  buildInputs = [ (texlive.combine {
                    inherit (texlive) collection-latexrecommended
                                      algorithmicx algorithms paralist
                                      listings csquotes etoolbox epsf
                                      tikz-qtree titlesec;
                  }) ];

  buildCommand = ''
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
  '';
}
