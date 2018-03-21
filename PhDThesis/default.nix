with builtins;
with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs.repo1609."00ef7f9";
with { defs = rec {
  inherit bibtex;

  tex = (texlive.combine {
    inherit (texlive)
      scheme-small tikzinclude;
  });

  isTex = path: hasSuffix ".tex" (baseNameOf path);

  render = { name, src }: runCommand "${name}.pdf"
    {
      inherit bibtex name src;
      buildInputs = [ tex ];
    }
    ''
      function go {
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape "$@"
      }

      cp -s "$src"/*  ./
      ln -s "$bibtex" ./Bibtex.bib

      go     "$name"
      bibtex "$name"
      go     "$name"
      go     "$name"
    '';

  outline = render {
    name = "outline";
    src  = attrsToDir { outline = ./outline.tex; };
  };

  thesis = withDeps [ outline ] (render {
    name = "thesis";
    src  = filterSource (path: type: isTex path) ./.;
  });

}; };

{ pdfOnly ? true }: if pdfOnly then defs.thesis else defs
