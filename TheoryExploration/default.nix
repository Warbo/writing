{pkgs ? import <nixpkgs> {}}:

with pkgs;
stdenv.mkDerivation {
  name = "ml4hs-paper1";
  buildInputs = [ md2pdf ];
}
