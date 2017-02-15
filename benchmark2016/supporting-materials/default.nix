with import <nixpkgs> {};

runCommand "support"
  {
    stabilisePlot = import ./stabilisePlot.nix;
  }
  ''
    mkdir "$out"
    cp -r "$stabilisePlot" "$out/stabilisePlot"
  ''
