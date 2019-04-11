# Resources used by multiple projects, including particular versions of nixpkgs
with builtins;
with rec {
  # Pinned versions of nixpkgs, nix-helpers, etc. which each project can use to
  # ensures they remain reproducible.

  repoSouce = http://chriswarbo.net/git;

  # Use the system's nixpkgs to fetch git repos (since they're fixed-output,
  # this shouldn't affect reproducibility). cleanSlate avoids user overrides.
  inherit (import <nixpkgs> cleanSlate) fetchFromGitHub fetchgit;

  # We don't know what version <nixpkgs> might be, so we check whether it's too
  # old for the 'overlays' argument, to avoid triggering an error.
  cleanSlate = if -1 == compareVersions (import <nixpkgs> {}).lib.nixpkgsVersion
                                        "1703"
                  then { config = {}; }
                  else { config = {}; overlays = []; };

  # Arbitrary, but known, version of nixpkgs to use as a base
  stable-nixpkgs-src = fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "f22817d";
    sha256 = "1cx5cfsp4iiwq8921c15chn1mhjgzydvhdcmrvjmqzinxyz71bzh";
  };

  # A stable package set which includes some overrides, for when we need them
  stable-configured = import stable-nixpkgs-src {
    config = import "${nix-config}/config.nix";
  };

  # Particular versions of our custom nix-config overrides
  nix-config = fetchgit {
    url    = "${repoSouce}/nix-config.git";
    rev    = "809056c";
    sha256 = "0gh6knckddy6l250qxp7v8nvwzfy24pasf8xl9gmpslx11s1ilpd";
  };

  warbo-packages-src = fetchgit {
    url    = "${repoSouce}/warbo-packages.git";
    rev    = "9f129aa";
    sha256 = "1v35m8xxqav8cq4g1hjn8yhzhaf9g4jyrmz9a26g7hk04ybjwc7k";
  };

  nix-helpers-src = (import "${warbo-packages-src}/helpers.nix" {}).nix-helpers;

  nixpkgs-joined = import stable-configured.repo1809 {
    config   = {};
    overlays = [
      (import "${nix-helpers-src}/overlay.nix")
      (import "${warbo-packages-src}/overlay.nix")
    ];
  };
};
rec {
  inherit nixpkgs-joined;
  bibtex = ../Bibtex.bib;
  styles = nixpkgs-joined.dirsToAttrs ./styles;
}
