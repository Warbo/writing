with { inherit (import ../resources) nixpkgs; };
with nixpkgs.repo1703.configless;

runCommand "CICM-2017-report"
  {
    source      = ./report.md;
    buildInputs = [
      pandoc
      (texlive.combine {
        inherit (texlive)
          scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
          algorithms frankenstein csquotes helvetic paralist chktex enumitem;
      })
    ];
  }
  ''
    mkdir "$out"
    pandoc --latex-engine=xelatex -o "$out/report.pdf"  "$source"
    pandoc --standalone           -o "$out/report.html" "$source"
  ''
