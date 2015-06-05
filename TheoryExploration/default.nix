with import <nixpkgs> {};

    # Get each tool from a specific git commit, to ensure reproducibility
let atCommit = name: rev: sha256:
               fetchgit {
                 inherit name rev sha256;
                 url  = "http://chriswarbo.net/git/${name}.git";
               };
    treefeatures1 = haskellPackages.callPackage (import (atCommit
                      "tree-features"
                      "ae8053b"
                      "1w71h7b1i91fdbxv62m3cbq045n1fdfp54h6bra2ccdj2snibx3y"
                    )) {};
    hs2ast1       = haskellPackages.callPackage (import (atCommit
                      "hs2ast"
                      "512572b"
                      "1lg8p0p30dp6pvbi007hlpxk1bnyxhfazzvgyqrx837da43ymm7f"
                    )) {};
    ml4hs1        = (import (atCommit
                      "ml4hs"
                      "9e15ed8"
                      "1qj8cg4425jb0lzhcap9fv0x6jxq4aai1q3rihmracixiqcq2gws"
                    )) { treefeatures = treefeatures1; hs2ast = hs2ast1; };
in stdenv.mkDerivation {
  name        = "theory-exploration-notes";
  buildInputs = [ ml4hs1 hs2ast1 ];
  #shellHook   = ''
  #  cp -ar "${h2a}" h2a
  #'';
}
