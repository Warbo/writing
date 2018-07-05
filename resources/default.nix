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
    "ffa6543" = "08hi2j38sy89sk5aildja453yyichm2jna8rxk4ad44h0m2wy47n";
    "2cc683b" = "1xm2jvia4n002jrk055c3csy8qvyjw9h0vilxzss0rb8ik23rn9g";
    "de1ceec" = "0km3jb3g80v3s6ja8v7nyk6jm1kd5j68yn68kyfdw800hx2qnz6c";
    "00ef7f9" = "1b7g4r144hwqa2a13cnfwmwxfkjd884pk4lqralxiqwbb0vr0nsw";
    "809056c" = "0gh6knckddy6l250qxp7v8nvwzfy24pasf8xl9gmpslx11s1ilpd";
  };

  # Particular versions of nixpkgs
  nixpkgs-repos = {
    inherit (stable-configured) repo1603 repo1609 repo1703 repo1709;
  };

  # All combinations of nixpkgs and nix-config versions
  nixpkgs =
    with unstable-nixpkgs.lib;
    mapAttrs
      (version: nixpkgs:
        { configless = nixpkgs-without-config version nixpkgs; } //
        mapAttrs (_: nixpkgs-with-config nixpkgs)
                 nix-configs)
      nixpkgs-repos;

  warbo-packages = mapAttrs
    (rev: sha256: import (unstable-nixpkgs.fetchgit {
      inherit rev sha256;
      url = "${repoSouce}/warbo-packages.git";
    }))
    {
      "c2ea27d" = "04aif1s3cxk27nybsxp571fmvswy5vbw0prq67y108sb49mm3288";
    };
};
rec {
  inherit nixpkgs warbo-packages;
  bibtex = ../Bibtex.bib;
  styles = stable-configured.dirsToAttrs ./styles;
}
