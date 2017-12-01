with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "paar16";
  src  = ./.;
  buildInputs = [
    bash
    gnumake
    (texlive.combine {
      inherit (texlive) scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms;
    })
  ];
}
