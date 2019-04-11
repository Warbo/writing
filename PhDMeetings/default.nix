with (import ../resources).nixpkgs;
with lib;
with {
  renderAll = dir: runCommand "phd-meetings-${dir}"
    {
      dir         = ./. + "/${dir}";
      buildInputs = [
        # LaTeX
        (texlive.combine { inherit (texlive) scheme-small; })

        # Graph drawing
        graphviz
        blockdiag

        # Document rendering
        pandocPkgs

        # Embedded code snippets
        #coq_mtac
        #treefeatures
        ditaa
        ditaaeps
        vim
        haskellPackages.ghc
        haskellPackages.QuickCheck

        # Automatic rendering
        inotifyTools
      ];
    }
    ''
      mkdir "$out"
      for F in "$dir"/*.md
      do
        NAME=$(basename "$F" .md)
        pandoc -o "$out/$NAME.pdf" "$F"
      done
    '';
};
genAttrs [ "2015-02-12" "2015-02-26" "2015-03-05" "2015-09-16" ]
         renderAll
