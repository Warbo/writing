with rec {
  inherit (import ../resources) bibtex nixpkgs styles;
  inherit (nixpkgs.repo1609.configless) runCommand;
};
runCommand "transfer-report.pdf"
  {
    inherit bibtex;
    buildInputs = [
      (texlive.combine { inherit (texlive) collection-latexrecommended; })
    ];
    src    = ./.;
    styles = [ styles."mathpartir.sty" styles."mmm.sty" styles."psfig.sty" ];
    cmd    = ''
      pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report
    '';
  }
  ''
    set -e
    echo "Putting resources in place" 1>&2
    ln -s "$bibtex" ./bibtex.bib
    for S in $styles
    do
      cp -s "$S" ./
    done

    echo "Rendering" 1>&2
    $cmd
    echo "RUNNING bibtex" 1>&2
    bibtex report
    $cmd
    $cmd

    [[ -e report.pdf ]] && cp report.pdf "$out"
  ''
