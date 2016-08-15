{ gnugrep, haskellPackages, pandoc, panhandle, panpipe, stdenv }:

stdenv.mkDerivation {
  name        = "theory-exploration-notes";
  src         = ./.;
  buildInputs = [

    # Document rendering tools
    pandoc
    haskellPackages.pandoc-citeproc
    panpipe
    panhandle

    # Misc shell tools
    gnugrep
  ];
}
