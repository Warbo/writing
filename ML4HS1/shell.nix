with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "ml4hs-paper1";
  buildInputs = [ pandoc panpipe panhandle ];
}
