with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs.repo1709."809056c";
runCommand "Chalmers-2015-03-25.pdf"
  {
    buildInputs = [ pandocPkgs texlive.combined.scheme-small ];
    src         = ./.;
  }
  ''
    cd "$src"
    pandoc -t beamer -o "$out" slides.md
  ''
