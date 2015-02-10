with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-meetings";
  src  = ./.;
  buildInputs = [
    pkgs.texLiveFull # LaTeX
    pkgs.emacs
    pkgs.ghostscript
  ];
}
