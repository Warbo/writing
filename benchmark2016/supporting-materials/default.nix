# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

with builtins;
with rec {
  # General utilities, etc. including nixpkgs and haskell-te
  inherit (import ./defs.nix)
    callPackage pkgs;

  # Raw benchmark data, i.e. how long each system takes to run
  inherit (callPackage ./benchmark-runs.nix {})
    ;

  # Precision/recall analysis of data, i.e. how "good" the output is
  inherit (callPackage ./precision-recall.nix)
    precisionRecallTable;

  # Comparisons between benchmarks
  inherit (callPackage ./differences.nix {})
    diffBetween;

  # Sanity checks, to look for dependencies/bias in the data
  inherit (callPackage stability.nix {})
    ;

  inherit (callPackage ./stabilisePlot.nix {})
    ;
};
{}
