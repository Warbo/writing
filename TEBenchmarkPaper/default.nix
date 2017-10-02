with rec {
  inherit (import ../resources) bibtex nixpkgs;
  inherit (nixpkgs.repo1609."00ef7f9") mkBin runCommand texlive unzip;
  inherit (import ./supporting-materials) latex;
};

runCommand "benchmark-article.pdf"
  {
    inherit bibtex latex;
    src         = ./.;
    buildInputs = [
      unzip

      (texlive.combine {
        inherit (texlive)
          scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
          frankenstein csquotes multirow;
      })

      (mkBin {
        name   = "render";
        script = ''
          #!/usr/bin/env bash
          exec pdflatex -interaction=nonstopmode \
                        -halt-on-error \
                        --shell-escape article
        '';
      })
    ];
  }
  ''
    cp -r "$src"/*  ./
    ln -s "$bibtex" ./Bibtex.bib
    unzip "$latex"

    render
    bibtex article
    render
    render

    mv article.pdf "$out"
  ''
