with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "balmoral-2015";
  buildInputs = [
    haskell.packages.ghc784.Agda
    md2pdf
  ];
}
