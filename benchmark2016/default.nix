with import <nixpkgs> {};
with builtins;

stdenv.mkDerivation {
  inherit (import ./supporting-materials) support;

  name        = "benchmark-article.pdf";
  src         = ./.;
  buildInputs = [
    bash
    gnumake
    (texlive.combine {
      inherit (texlive)
        scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
        frankenstein csquotes;
    })
  ];
  buildPhase =
    let cmd = "pdflatex -interaction=nonstopmode -halt-on-error --shell-escape article";
     in ''
          cp -r "$support" ./support
          cp ${../Bibtex.bib} ./Bibtex.bib
          ${cmd}
          bibtex article
          ${cmd}
          ${cmd}
        '';

  installPhase = ''
    cp article.pdf "$out"
  '';
}
