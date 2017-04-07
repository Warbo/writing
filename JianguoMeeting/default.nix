with import <nixpkgs> {};

runCommand "render"
  {
    buildInputs    = [ goat pandoc panpipe panhandle ];
    file           = ./writeup.md;
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";
  }
  ''
    pandoc -s -t html --filter panpipe --filter panhandle < "$file" > "$out"
  ''
