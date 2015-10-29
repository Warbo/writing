with import <nixpkgs> {};

    # Fetch a particular git commit, to allow comparison of different approaches
let atCommit = name: rev: sha256:
               fetchgit {
                 inherit name rev sha256;
                 url  = "http://chriswarbo.net/git/${name}.git";
               };
    hsPkgs = te-unstable;
    hs = hsPkgs.callPackage;

    # Source code to experiment on
    hs2astSrc = atCommit "hs2ast" "512572b"
                         "1lg8p0p30dp6pvbi007hlpxk1bnyxhfazzvgyqrx837da43ymm7f";

    # Tools to experiment with
    treefeatures1 = hs (import (atCommit
                      "tree-features"
                      "ae8053b"
                      "1w71h7b1i91fdbxv62m3cbq045n1fdfp54h6bra2ccdj2snibx3y"
                    )) {};
    hs2ast1       = hs (import hs2astSrc) {};
    ml4hs1 = import /home/chris/Programming/ML4HS;
    ml4hs2        = (import (atCommit
                      "ml4hs"
                      "9e15ed8"
                      "1qj8cg4425jb0lzhcap9fv0x6jxq4aai1q3rihmracixiqcq2gws"
                    )) {
                      treefeatures = treefeatures1;
                      hs2ast       = hs2ast1;
                    };
in stdenv.mkDerivation {
  name        = "theory-exploration-notes";
  buildInputs = [
    # Tool for running experiments *with*
    ml4hs1 #haskellPackages.criterion

    # Data for running experiments *on*
    hs2ast1 haskellPackages.hoogle

    # Document rendering tools
    pandoc
    haskellPackages.pandoc-citeproc
    texLiveFull
    (hs (atCommit "panpipe"
                  "a3a40e9"
                  "0sajlq926yr4684vbzmjh2209fnmrx1p1lqfbhxj5j0h166424ak") {})
    (hs (atCommit "panhandle"
                  "11ab103"
                  "0ix7wd3k5q50ydanrv4sb2nfjbz32c4y38i4qzirrqf3dvbv734m") {})

    # Misc shell tools
    wget # For Hoogle
    gnugrep
  ];

  shellHook = ''
    export HS2ASTSRC='${hs2astSrc}'
    test -d hoogle || (mkdir -p hoogle; hoogle data --datadir=./hoogle)
  '';
}
