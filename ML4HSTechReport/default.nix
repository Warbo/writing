with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "ml4hs-tech-report";
  src  = ./.;
  installPhase = ''
    cp report.pdf "$out"
  '';
}
