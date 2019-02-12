with (import ../resources).nixpkgs-joined;

runCommand "render"
  {
    buildInputs    = [ goat pandocPkgs ];
    src            = ./.;
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";
  }
  ''
    cd "$src"
    pandoc --standalone --to html --mathml \
           --filter panpipe --filter panhandle < writeup.md > "$out"
  ''
