with { inherit (import ../resources) bibtex nixpkgs styles; };
with nixpkgs;

runCommand "transfer-report.pdf"
  {
    inherit bibtex;
    buildInputs = [
      jq
      (texlive.combine {
        inherit (texlive)
          collection-latexrecommended scheme-small tikzinclude tikz-qtree
          algorithmicx algorithm2e algorithms frankenstein csquotes helvetic
          paralist chktex enumitem listings preprint epsf titlesec cm-super;
        })
    ];
    src    = ./.;
    styles = builtins.toJSON styles;
    cmd    = ''
      pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report
    '';
  }
  ''
    set -e
    echo "Putting resources in place" 1>&2
    cp -sr "$src"/*  ./
    ln -s  "$bibtex" ./bibtex.bib
    echo "$styles" | jq -rc 'keys | .[]' | while read -r S
    do
      F=$(echo "$styles" | jq -r -c --arg s "$S" '.[$s]')
      ln -s "$F" "./$S"
    done

    echo "Removing existing file" 1>&2
    rm report.pdf

    echo "Rendering" 1>&2
    $cmd
    bibtex report
    $cmd
    $cmd

    cp report.pdf "$out"
  ''
