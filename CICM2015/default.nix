with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "cicm-2015";

  src = ./.;

  buildInputs = [
    texLive
  ];
}
