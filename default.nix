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
    pkgs.haskellPackages.pandoc
    pkgs.haskellPackages.pandocCiteproc
    panpipe
    panhandle

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
