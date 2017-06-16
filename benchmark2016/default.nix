with import <nixpkgs> {};
with builtins;

stdenv.mkDerivation {
  inherit (import ./supporting-materials) buildInputs support latex;

  name = "benchmark-article.pdf";
  src  = ./article.tex;

  unpackPhase = "true";
  buildPhase  = ''
    function render {
      pdflatex -interaction=nonstopmode -halt-on-error \
               --shell-escape article
    }

    cp "$src" article.tex
    cp -r "$support" ./support
    ln -s ${../Bibtex.bib} ./Bibtex.bib
    unzip "$latex"

    render
    bibtex article
    render
    render
  '';

  installPhase = ''
    cp article.pdf "$out"
  '';
}
