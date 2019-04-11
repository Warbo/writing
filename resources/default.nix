# Resources used by multiple projects, including particular versions of nixpkgs
with builtins;
with rec {
  # Allow each project to mix and match the particular versions they want of
  # nixpkgs, nix-config, etc. This ensures they remain reproducible.

  repoSouce = http://chriswarbo.net/git;

  # Load nixpkg versions with and without custom overrides
  nixpkgs-with-config = nixpkgs: config: import nixpkgs {
    config = import "${config}/config.nix";
  };
  nixpkgs-without-config = version: nixpkgs:
    import nixpkgs (if compareVersions version "repo1703" == -1
                       then { config = {}; }
                       else { config = {}; overlays = []; });

  # Whichever nixpkgs the system is using. Only use this to get fixed output
  # derivations, otherwise we risk breaking reproducibility.
  unstable-nixpkgs = nixpkgs-without-config
    "repo${(import <nixpkgs> {}).lib.nixpkgsVersion}"
    <nixpkgs>;

  # Arbitrary, but known, versions of nixpkgs and nix-config, used as a base
  stable-nixpkgs-src = unstable-nixpkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "f22817d";
    sha256 = "1cx5cfsp4iiwq8921c15chn1mhjgzydvhdcmrvjmqzinxyz71bzh";
  };

  # A stable package set which includes some overrides, for when we need them
  stable-configured = nixpkgs-with-config stable-nixpkgs-src
                                          nix-configs."809056c";

  inherit (unstable-nixpkgs.lib) mapAttrs;

  # Particular versions of our custom nix-config overrides
  nix-config-url = "${repoSouce}/nix-config.git";
  nix-configs    = mapAttrs (rev: sha256: unstable-nixpkgs.fetchgit {
                                            inherit rev sha256;
                                            url = nix-config-url;
                                          }) {
    "809056c" = "0gh6knckddy6l250qxp7v8nvwzfy24pasf8xl9gmpslx11s1ilpd";
  };

  warbo-packages-src = unstable-nixpkgs.fetchgit {
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
  styles = stable-configured.dirsToAttrs ./styles;
}
