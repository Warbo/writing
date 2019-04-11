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

  # Fetch our custom package overlay. This repo also includes a pinned version
  # of nix-helpers, so we use that (to avoid repeating ourselves).
  warbo-packages-src =
    with { repoSouce = http://chriswarbo.net/git; };
    fetchgit {
      url    = "${repoSouce}/warbo-packages.git";
      rev    = "9f129aa";
      sha256 = "1v35m8xxqav8cq4g1hjn8yhzhaf9g4jyrmz9a26g7hk04ybjwc7k";
    };

  # Loads an overlay of helper functions for Nix, from the pinned version we
  # keep in warbo-packages.
  nix-helpers-overlays =
    with { src = (import "${warbo-packages-src}/helpers.nix" {}).nix-helpers; };
    [ (import "${src}/overlay.nix") ];

  # A pinned version of nixpkgs, with nix-helpers and warbo-packages overlays
  nixpkgs-joined =
    with rec {
      # Arbitrary, but known, version of nixpkgs to use as a base
      stable = fetchFromGitHub {
        owner  = "NixOS";
        repo   = "nixpkgs";
        rev    = "6a3f5bc";
        sha256 = "1ib96has10v5nr6bzf7v8kw7yzww8zanxgw2qi1ll1sbv6kj6zpd";
      };

      # Overlay with nix-helpers to make repoXXXX definitions available
      stable-configured = import stable { overlays = nix-helpers-overlays; };
    };
    # Pick a version of nixpkgs and add both of our overlays to it
    import stable-configured.repo1809 {
      config   = {};
      overlays = nix-helpers-overlays ++ [
        (import "${warbo-packages-src}/overlay.nix")
      ];
    };
};
rec {
  inherit nixpkgs-joined;
  bibtex = ../Bibtex.bib;
  styles = nixpkgs-joined.dirsToAttrs ./styles;
}
