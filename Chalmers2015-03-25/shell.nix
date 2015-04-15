with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "chalmers-slides";
  buildInputs = [ md2pdf ];
}
