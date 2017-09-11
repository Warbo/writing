with import <nixpkgs> {};
with builtins;

stdenv.mkDerivation {
  inherit (import ./supporting-materials) /*support*/ latex;

  name        = "benchmark-article.pdf";
  src         = ./.;
  buildInputs = [
    bash
    gnumake
    unzip
    (texlive.combine {
      inherit (texlive)
        scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
        frankenstein csquotes multirow;
    })
  ];
  buildPhase =
    let cmd = "pdflatex -interaction=nonstopmode -halt-on-error --shell-escape article";
     in ''
          #cp -r "$support" ./support
          ln -s ${../Bibtex.bib} ./Bibtex.bib
          unzip "$latex"
          find .
          ${cmd}
          bibtex article
          ${cmd}
          ${cmd}
        '';

  installPhase = ''
    cp article.pdf "$out"
  '';
}
