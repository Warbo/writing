with rec {
  nixpkgs = (import ../resources).nixpkgs.repo1703."00ef7f9";

  results = import ./default.nix { inherit nixpkgs; };

  inherit (results.nix-helpers) allDrvsIn withDeps;
};
withDeps (allDrvsIn results.checks) results.paper
