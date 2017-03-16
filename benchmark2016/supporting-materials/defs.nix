# Useful stuff, which we'll use over and over

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
  callPackage = pkgs.newScope {
    inherit haskell-te-src haskell-te haskell-te-defs miller;
  };

  # This repository contains the software we're discussing, and its benchmarks
  haskell-te-src  = pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "e3527b7";
    sha256 = "0axxa3slnwc1sinwawixbhh1rr876a1gnj3b4ggvbjzpl2i26ba2";
  };

  # This is a package, which provides the benchmarks as commands
  haskell-te = import haskell-te-src;

  # These are definitions used by the above package, which we can reuse
  haskell-te-defs = import "${haskell-te-src}/nix-support" {};

  # A commandline tool for manipulating CSV data, performing statistics, etc.
  miller = pkgs.callPackage ./miller.nix {};
}
