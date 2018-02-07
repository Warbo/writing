with builtins;
with { inherit (import ../resources) bibtex nixpkgs styles; };
with nixpkgs.repo1703."00ef7f9";

runCommand "bucketing.pdf"
  {
    inherit bibtex;
    cmd         = ''pdflatex -interaction=nonstopmode \
                             -halt-on-error --shell-escape report'';
    src         = ./.;
    styles      = attrValues styles;
    buildInputs = [
      bash
      gnumake
      (texlive.combine {
        inherit (texlive) scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms;
      })
    ];
  }
  ''
    cp "$src"      ./src
    chmod -r +w    ./src
    cp "$bibtex"   ./src/Bibtex.bib

    for STYLE in $styles
    do
      cp "$STYLE" ./src
    done

    cd ./src

    $cmd
    echo "RUNNING bibtex"
	  bibtex report
    $cmd
    $cmd

    cp "report.pdf" "$out"
  ''
