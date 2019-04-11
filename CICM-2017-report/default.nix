with (import ../resources).nixpkgs;

{
  pdf = runCommand "CICM-2017-report.pdf"
    {
      source      = ./report.md;
      buildInputs = [
        pandocPkgs
        (texlive.combine {
          inherit (texlive)
            scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
            algorithms frankenstein csquotes helvetic paralist chktex enumitem;
        })
      ];
    }
    ''
      pandoc --latex-engine=xelatex -o "$out"  "$source"
    '';

  html = runCommand "CICM-2017-report.html"
    {
      source      = ./report.md;
      buildInputs = [ pandocPkgs ];
    }
    ''
      pandoc --standalone -o "$out" "$source"
    '';
}
