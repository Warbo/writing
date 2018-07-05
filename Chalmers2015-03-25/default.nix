with import ../resources;
with nixpkgs.repo1709.configless;
with warbo-packages."c2ea27d";
runCommand "Chalmers-2015-03-25.pdf"
  {
    buildInputs = [ pandocPkgs texlive.combined.scheme-small ];
    src         = ./.;
  }
  ''
    cd "$src"
    pandoc -t beamer -o "$out" slides.md
  ''
