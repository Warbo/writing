with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "phd-meetings";
  src  = ./.;
  buildInputs = [
    # LaTeX
    pkgs.texLiveFull

    # Graph drawing
    pkgs.graphviz
    pkgs.blockdiag

    # Document rendering
    (import ../resources).warbo-packages."c2ea27d".pandocPkgs

    # Embedded code snippets
    #coq_mtac
    #treefeatures
    ditaa
    ditaaeps
    vim
    haskellPackages.ghc
    haskellPackages.QuickCheck

    # Automatic rendering
    pkgs.inotifyTools
  ];
}
