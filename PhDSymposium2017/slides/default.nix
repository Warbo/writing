with rec {
  inherit (import ../../resources)        bibtex nixpkgs;
  inherit (nixpkgs.repo1609."2cc683b")
    callPackage ditaa ghostscript glibcLocales imagemagick jq runCommand;
  inherit (callPackage ../support.nix {}) renderers tex;
};

runCommand "phd-symposium-2017-slides.html"
  {
    inherit bibtex;
    buildInputs    = [ ditaa ghostscript imagemagick jq ] ++ renderers;

    # Required for Haskell and Perl to not barf at unicode
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

    slides         = ./slides.md;
    TABLE_IMAGE    = ./table.png;
  }
  ''
    export HOME="$PWD"
    cp "${./table.png}" ./
    pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
                    --filter panpipe --filter panhandle \
                    --bibliography="$bibtex" \
                    -o "$out" "$slides"
  ''
