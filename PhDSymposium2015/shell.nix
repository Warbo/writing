with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-symposium-2015";
  buildInputs = [ (import ../resources).warbo-packages."c2ea27d".pandocPkgs ];
}
