with import <nixpkgs> {};

runCommand "ml4hs-paper1"
  {
    buildInputs = [ (import ../resources).warbo-packages."c2ea27d".pandocPkgs ];
    src         = ./ml4hs1.md;
  }
  ''
    mkdir "$out"
    pandoc --filter panpipe --filter panhandle -o "$out/ml4hs1.pdf" "$src"
  ''
