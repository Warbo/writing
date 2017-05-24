with import <nixpkgs> {};
with (callPackage ../support.nix {});

{ bibtex ? ../../Bibtex.bib }:
runCommand "phd-symposium-2017-slides.html"
  {
    inherit bibtex;
    buildInputs = [ ditaa ghostscript imagemagick jq ] ++ renderers;

    # Required for Haskell and Perl to not barf at unicode
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

    slides   = ./slides.md;

    TABLE_IMAGE = ./table.png;
  }
  ''
    export HOME="$PWD"
    cp "${./table.png}" ./
    pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
                    --filter panpipe --filter panhandle \
                    --bibliography="$bibtex" \
                    -o "$out" "$slides"
  ''
