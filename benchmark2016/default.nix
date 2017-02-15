with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "benchmark-article";
  src  = ./.;
  support     = import ./supporting-materials;
  buildInputs = [
    bash
    gnumake
    (texlive.combine {
      inherit (texlive) scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms;
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
