with { inherit (import ../resources) nixpkgs warbo-packages; };
with nixpkgs.repo1703."00ef7f9";

{
  pdf = runCommand "CICM-2017-report.pdf"
    {
      source      = ./report.md;
      buildInputs = [
        warbo-packages."c2ea27d".pandocPkgs
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
