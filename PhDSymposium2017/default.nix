{
  # These depend on haskell-te, which rebuilds the world
  #inherit ((import ../resources).nixpkgs.callPackage ./support.nix {})
  #  qualityPlot runtimePlot;

  abstract = import ./abstract;
  slides   = import ./slides;
}
