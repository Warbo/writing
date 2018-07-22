with import ../resources;
with {
  pkgs = nixpkgs.repo1609.configless;
  ours = warbo-packages."c2ea27d";
};
pkgs.stdenv.mkDerivation {
  name = "balmoral-2015";
  buildInputs = [
    pkgs.haskell.packages.ghc784.Agda
    ours.md2pdf
  ];
}
