with (import ../resources).nixpkgs;

runCommand "ml4hs-paper1"
  {
    buildInputs = [ pandocPkgs texlive.combined.scheme-small ];
    src         = ./ml4hs1.md;
  }
  ''
    mkdir "$out"
    pandoc --filter panpipe --filter panhandle -o "$out/ml4hs1.pdf" "$src"
  ''
