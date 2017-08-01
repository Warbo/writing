with import <nixpkgs> {};

runCommand "CICM-2017-report"
  {
    buildInputs = [
      pandoc
      (texlive.combine {
        inherit (texlive)
          scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
          algorithms frankenstein csquotes helvetic paralist chktex enumitem;
      })
    ];
    source      = ./report.md;
  }
  ''
    mkdir "$out"
    pandoc --latex-engine=xelatex -o "$out/report.pdf"  "$source"
    pandoc --standalone           -o "$out/report.html" "$source"
  ''
