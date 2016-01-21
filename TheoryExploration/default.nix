with import <nixpkgs> {};

stdenv.mkDerivation {
  name        = "theory-exploration-notes";
  buildInputs = [
    ml4hs #haskellPackages.criterion
    HS2AST

    # Document rendering tools
    pandoc
    haskellPackages.pandoc-citeproc
    panpipe
    panhandle

    # Misc shell tools
    gnugrep
  ];
}
