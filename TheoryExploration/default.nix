    # 2 stage bootstrap. Use fetchgit from <nixpkgs> to get some version of
    # nix-config
let bootSrc  = (import <nixpkgs> {}).fetchgit {
                 url    = cfgUrl;
                 rev    = "be310e2"; # First commit with default.nix
                 sha256 = "166lzyxyh2d2ivm6bf3nrb55p00cf7q0pv1gskj8crxsx4ym8w2h";
               };
    bootPkgs = import "${bootSrc}" { pkgFunc = import <nixpkgs>; };

    # Use bootPkgs.latestGit to get the latest nix-config
    pkgSrc = bootPkgs.latestGit { url = cfgUrl; };
    pkgs   = import "${pkgSrc}" { pkgFunc = import <nixpkgs>; };

    cfgUrl = http://chriswarbo.net/git/nix-config.git;

 in with pkgs;
    stdenv.mkDerivation {
      name        = "theory-exploration-notes";
      src         = ./.;
      buildInputs = [

        # Document rendering tools
        pandoc
        haskellPackages.pandoc-citeproc
        panpipe
        panhandle

        # Misc shell tools
        gnugrep
      ];
    }
