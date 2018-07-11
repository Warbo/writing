with { inherit (import ../resources) nixpkgs warbo-packages; };
with nixpkgs.repo1703."2cc683b";
runCommand "render"
  {
    buildInputs    = [ goat warbo-packages."c2ea27d".pandocPkgs ];
    src            = ./.;
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";
  }
  ''
    cd "$src"
    pandoc --standalone --to html --mathml \
           --filter panpipe --filter panhandle < writeup.md > "$out"
  ''
