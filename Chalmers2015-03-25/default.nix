with builtins;
with (import ../resources).nixpkgs-joined;
with lib;

runCommand "Chalmers-2015-03-25.pdf"
  {
    buildInputs = [ pandocPkgs texlive.combined.scheme-small ];
    src         = filterSource (path: type: any (x: hasSuffix x path) [
                                 ".jpeg" ".jpg" ".md" ".png" ".svg"
                               ])
                               ./.;
  }
  ''
    cd "$src"
    pandoc -t beamer -o "$out" slides.md
  ''
