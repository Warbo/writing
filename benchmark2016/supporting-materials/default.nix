# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

with builtins;
with rec {
  # General utilities, etc. including nixpkgs and haskell-te
  inherit (import ./defs.nix)
    callPackage;

  # Raw benchmark data, i.e. how long each system takes to run
  inherit (callPackage ./benchmark-runs.nix {})
    sampledBenchmarkData sampledTestData;

  # Precision/recall analysis of data, i.e. how "good" the output is
  inherit (callPackage ./precision-recall.nix {})
    precisionRecallTable;

  # Comparisons between benchmarks
  inherit (callPackage ./differences.nix {})
    diffBetween;

  # Sanity checks, to look for dependencies/bias in the data
  inherit (callPackage ./stability.nix {
            inherit sampledBenchmarkData sampledTestData;
          })
    examplePlots plotTests stabilityPlots;
};

{
  # Not directly used by the paper, but useful for debugging, e.g. via nix-repl.
  debug = {
    inherit examplePlots plotTests sampledBenchmarkData sampledTestData
            stabilityPlots;
  };

  # Force tests to run before we even attempt to gather data; otherwise we might
  # spend ages running experiments, which then get mangled by some trivial typo.
  support = assert all (test: import "${test}") [ plotTests ]; ./default.nix;
}
