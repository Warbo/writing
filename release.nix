    # Use fetchgit from <nixpkgs> to get some version of nix-config
let bootPkgs = call ((import <nixpkgs> {}).fetchgit {
                 url    = cfgUrl;
                 rev    = "be310e2";
                 sha256 = "166lzyxyh2d2ivm6bf3nrb55p00cf7q0pv1gskj8crxsx4ym8w2h";
               });

    # Use bootPkgs.latestGit to get the latest nix-config
    pkgs = call (bootPkgs.latestGit { url = cfgUrl; });

    call   = f: import "${f}" { pkgFunc = import <nixpkgs>; };
    cfgUrl = http://chriswarbo.net/git/nix-config.git;

in with pkgs;
{
  ML4HSTechReport   = callPackage ./ML4HSTechReport   {};
  theoryExploration = callPackage ./TheoryExploration {};
}
