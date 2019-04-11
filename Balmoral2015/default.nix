with builtins;
with (import ../resources).nixpkgs;
with lib;

runCommand "balmoral-2015"
  {
    buildInputs = [
      glibc
      graphviz
      (nixpkgs1603.haskellPackages.ghcWithPackages (hs: [ hs.Agda ]))
      pandocPkgs
    ];

    markdown = filterSource (path: type: hasSuffix ".md"   path ||
                                         hasSuffix ".agda" path)
                            ./.;
  }
  ''
    mkdir "$out"
    cd "$markdown"
    for F in *.md
    do
      NAME=$(basename "$F" .md)
      echo "Rendering $NAME" 1>&2
      pandoc --filter panpipe   \
             --filter panhandle \
             -w dzslides        \
             --standalone       \
             -o "$out/$NAME.html" "$F"
    done
  ''
