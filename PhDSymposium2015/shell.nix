with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-symposium-2015";
  buildInputs = [ md2pdf ];
}
