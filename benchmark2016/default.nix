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
      inherit (texlive) scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms;
    })
  ];
  buildPhase =
    let cmd = "pdflatex -interaction=nonstopmode -halt-on-error --shell-escape article";
     in ''
          if [[ -n "$SKIP_DATA" ]]
          then
            sed -i article.tex -e 's/Warburton/Warburton (TESTING DATA)/g'
          fi

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
