# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

with builtins;

rec {
  # All definitions; useful for debugging
  debug = rec {

    # General utilities, etc. including nixpkgs and haskell-te
    defs = import ./defs.nix;
    inherit (defs)
      callPackage attrsToDir;

    # Raw benchmark data, i.e. how long each system takes to run
    benchmark-runs = callPackage ./benchmark-runs.nix {};
    inherit (benchmark-runs)
      sampledBenchmarkData sampledTestData;

    # Raw bucketing data, i.e. how many equations we throw away by bucketing
    bucketing-runs = callPackage ./bucketing-runs.nix {};

    # Precision/recall analysis of data, i.e. how "good" the output is
    precision-recall = callPackage ./precision-recall.nix {};
    inherit (precision-recall)
      precisionRecallTable;

    # Comparisons between benchmarks
    differences = callPackage ./differences.nix {
      inherit sampledBenchmarkData sampledTestData;
    };
    inherit (differences)
      diffBetween;

    # Sanity checks, to look for dependencies/bias in the data
    stability = callPackage ./stability.nix {
      inherit sampledBenchmarkData sampledTestData;
    };
    inherit (stability)
      examplePlots plotTests stabilityPlots;
  };

  # The definitions required by the paper. We force tests to run before allowing
  # any data access; otherwise we might spend ages running experiments, which
  # then get mangled by some trivial typo.
  support = assert all (test: import "${test}") (with debug; [ plotTests ]);
            with debug; attrsToDir {
              "bucketing-graph.png" = bucketing-runs.bucketing-graph;
            };
}
