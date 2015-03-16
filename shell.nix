with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "chalmers-slides";
  buildInputs = [ pandoc texLiveFull inotifyTools ];
  shellHook = ''
    export PATH="$PATH:~/warbo-utilities/writing/"
  '';
}
