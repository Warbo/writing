with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "ml4hs-paper1";
  buildInputs = [ (import ../resources).warbo-packages."c2ea27d".pandocPkgs ];
}
