with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-meetings";
  src  = ./.;
  buildInputs = [
    pkgs.texLiveFull # LaTeX
    pkgs.graphviz
    pkgs.blockdiag
    pkgs.haskellPackages.pandoc
    pkgs.haskellPackages.pandocCiteproc
    panpipe
    panhandle
    coq_mtac
    treefeatures
  ];
}
