with builtins;
with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs.repo1609."00ef7f9";
with lib;
with { defs = rec {
  inherit bibtex;

  tex = (texlive.combine {
    inherit (texlive)
      scheme-small tikzinclude csquotes;
  });

  isTex = path: hasSuffix ".tex" (baseNameOf path);

  render = { file, src }: runCommand "${file}.pdf"
    {
      inherit bibtex file src;
      buildInputs = [ tex ];
    }
    ''
      function go {
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape "$@"
      }

      cp -s "$src"/*  ./
      ln -s "$bibtex" ./Bibtex.bib

      go     "$file"
      #bibtex "$file"
      go     "$file"
      go     "$file"

      cp "$file.pdf" "$out"
    '';

  outline = render {
    file = "outline";
    src  = attrsToDirs { outline = ./outline.tex; };
  };

  thesis = withDeps [ outline ] (render {
    file = "thesis";
    src  = filterSource (path: type: isTex path) ./.;
  });

  pdfs = attrsToDirs {
    "outline.pdf" = outline;
    "thesis.pdf"  = thesis;
  };

}; };

{ pdfOnly ? true }: if pdfOnly then defs.pdfs else defs
