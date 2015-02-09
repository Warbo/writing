with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-meetings";
  src  = ./.;
  buildInputs = [
    (hiPrio pkgs.texLive)
    pkgs.texLiveBeamer
    pkgs.texLiveExtra
    pkgs.emacs
  ];
}
