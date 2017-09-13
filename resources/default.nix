# Resources used by multiple projects, including particular versions of nixpkgs
with builtins;
with rec {
  # Allow each project to mix and match the particular versions they want of
  # nixpkgs and nix-config (if any). This ensures they remain reproducible.

  # Load nixpkg versions with and without custom overrides
  nixpkgs-with-config = nixpkgs: config: import nixpkgs {
    config = import "${config}/config.nix";
  };
  nixpkgs-without-config = nixpkgs: import nixpkgs { config = {}; };

  # Whichever nixpkgs the system is using. Only use this to get fixed output
  # derivations, otherwise we risk breaking reproducibility.
  unstable-nixpkgs = nixpkgs-without-config <nixpkgs>;

  # Arbitrary, but known, versions of nixpkgs and nix-config, used as a base
  stable-nixpkgs-src = unstable-nixpkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "16.09";
    sha256 = "1cx5cfsp4iiwq8921c15chn1mhjgzydvhdcmrvjmqzinxyz71bzh";
  };
  stable-nixpkgs = nixpkgs-without-config stable-nixpkgs-src;

  # A stable package set which includes some overrides, for when we need them
  stable-configured = nixpkgs-with-config stable-nixpkgs-src
                                          nix-configs."2cc683b";

  inherit (stable-nixpkgs.lib) mapAttrs;

  # Particular versions of our custom nix-config overrides
  nix-config-url = http://chriswarbo.net/git/nix-config.git;
  nix-configs    = mapAttrs (rev: sha256: stable-nixpkgs.fetchgit {
                                            inherit rev sha256;
                                            url = nix-config-url;
                                          }) {
    "ffa6543" = "08hi2j38sy89sk5aildja453yyichm2jna8rxk4ad44h0m2wy47n";
    "2cc683b" = "1xm2jvia4n002jrk055c3csy8qvyjw9h0vilxzss0rb8ik23rn9g";
  };

  # Particular versions of nixpkgs
  nixpkgs-repos = { inherit (stable-configured) repo1603 repo1609 repo1703; };

  # All combinations of nixpkgs and nix-config versions
  nixpkgs =
    with stable-nixpkgs.lib;
    mapAttrs
      (_: nixpkgs: { configless = nixpkgs-without-config nixpkgs; } //
                   mapAttrs (_: nixpkgs-with-config nixpkgs)
                            nix-configs)
      nixpkgs-repos;
};
rec {
  inherit nixpkgs;
  bibtex = ../Bibtex.bib;
  styles = stable-configured.dirsToAttrs ./styles;
}
