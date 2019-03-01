with rec {
  nixpkgs = (import ../resources).nixpkgs-joined;

  results = import ./default.nix;

  inherit (nixpkgs) allDrvsIn withDeps;
};
withDeps (allDrvsIn results.checks) results.paper
