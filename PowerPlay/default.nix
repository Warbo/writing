with import ../resources;
with nixpkgs.repo1703."00ef7f9";
with {
  tex = texlive.combine {
    inherit (texlive)
      scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
      frankenstein csquotes multirow type1cm;
  };

  render = mkBin {
    name   = "render";
    script = ''
      #!/usr/bin/env bash
      function go {
        pdflatex -interaction=nonstopmode \
                 -halt-on-error           \
                 --shell-escape "$1"
      }

      go
      bibtex "$1"
      go
      go
    '';
  };
};
runCommand "powerplay.pdf"
  {
    inherit bibtex;
    buildInputs = [ render tex ];
    src = ./article.tex;
  }
  ''
    set -e
    cp "$src" ./article.tex
    cp "$bibtex" ./Bibtex.bib
    render article
  '';
