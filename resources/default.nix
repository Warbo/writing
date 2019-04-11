# Resources used by multiple projects, including pinned versions of nixpkgs,
# nix-helpers, etc. to ensure reproducibility.
with builtins;
with rec {
  # Use the system's nixpkgs to fetch git repos (since they're fixed-output,
  # this shouldn't affect reproducibility). cleanSlate avoids user overrides.
  inherit (import <nixpkgs> cleanSlate) fetchFromGitHub fetchgit;

  # We don't know what version <nixpkgs> might be, so we check whether it's too
  # old for the 'overlays' argument, to avoid triggering an error.
  cleanSlate = if -1 == compareVersions (import <nixpkgs> {}).lib.nixpkgsVersion
                                        "1703"
                  then { config = {}; }
                  else { config = {}; overlays = []; };

  # Adds our custom overlays to the given nixpkgs version
  overlay = nixpkgs:
    with rec {
      # This overlay defines custom packages. The repo also includes a pinned
      # version of nix-helpers (which saves having to repeat ourselves).
      packages-src = fetchgit {
        url    = http://chriswarbo.net/git/warbo-packages.git;
        rev    = "9f129aa";
        sha256 = "1v35m8xxqav8cq4g1hjn8yhzhaf9g4jyrmz9a26g7hk04ybjwc7k";
      };

      # This defines helper functions for Nix.
      helpers-src = (import "${packages-src}/helpers.nix" {}).nix-helpers;
    };
    import nixpkgs {
      config   = {};
      overlays = [
        (import "${helpers-src}/overlay.nix" )
        (import "${packages-src}/overlay.nix")
      ];
    };

  # A pinned version of nixpkgs with our overlays
  nixpkgs-joined =
    with rec {
      # Arbitrary, but known, version of nixpkgs to use as a base
      stable = overlay (fetchFromGitHub {
        owner  = "NixOS";
        repo   = "nixpkgs";
        rev    = "6a3f5bc";
        sha256 = "1ib96has10v5nr6bzf7v8kw7yzww8zanxgw2qi1ll1sbv6kj6zpd";
      });
    };
    # Pick a version of nixpkgs and add both of our overlays to it
    overlay stable.repo1809;
};
rec {
  inherit nixpkgs-joined;
  bibtex = ../Bibtex.bib;
  styles = nixpkgs-joined.dirsToAttrs ./styles;
}
