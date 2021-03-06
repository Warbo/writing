# Useful stuff, which we'll use over and over

with builtins;
rec {
  # Nixpkgs, the main Nix package repository. We assume there's some version
  # available at the path <nixpkgs>, but using it willy nilly could affect our
  # reproducibility. Instead, we only use this 'ambient' nixpkgs to fetch a
  # fixed, stable version of nixpkgs which is the one we expose for use.
  pkgs = let defPkgs = import <nixpkgs> {};
          in import (defPkgs.fetchFromGitHub {
               owner  = "NixOS";
               repo   = "nixpkgs";
               rev    = "16.09";
               sha256 = "1cx5cfsp4iiwq8921c15chn1mhjgzydvhdcmrvjmqzinxyz71bzh";
             }) { config = {}; };

  # callPackage automatically fill in function arguments, if they're defined in
  # pkgs or the extra set we provide here
  callPackage = pkgs.newScope { inherit miller; };

  # A commandline tool for manipulating CSV data, performing statistics, etc.
  miller = pkgs.callPackage ./miller.nix {};

  # Take in { "foo/bar" = A; "baz" = B; ... } and produce a directory containing
  # symlinks foo/bar -> ${A}, baz -> ${B}, etc.
  attrsToDir = attrs:
    with rec {
      cmds  = map (name: let val = attrs."${name}";
                          in ''
                               DIR=$(dirname "${name}")
                               mkdir -p "$out/$DIR"
                               ln -s "${val}" "$out/${name}"
                             '')
                  (attrNames attrs);
    };
    pkgs.runCommand "attrsToDir" {} ''
      mkdir -p "$out"
      ${concatStringsSep "\n" cmds}
    '';
}
