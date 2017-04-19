with import <nixpkgs> {};

with rec {
  tex = callPackage ../tex.nix {};
};

runCommand "phd-symposium-2017-slides.html"
  {
    buildInputs = [ ditaa ghostscript haskellPackages.pandoc-citeproc
                    imagemagick pandoc panpipe panhandle tex ];

    # Required for Haskell and Perl to not barf at unicode
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

    slides   = ./slides.md;
  }
  ''
    export HOME="$PWD"

    pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
                    --filter panpipe --filter panhandle \
                    -o "$out" "$slides"
  ''
