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
    sampledBenchmarkData;

  # Precision/recall analysis of data, i.e. how "good" the output is
  inherit (callPackage ./precision-recall.nix {})
    precisionRecallTable;

  # Comparisons between benchmarks
  inherit (callPackage ./differences.nix {})
    diffBetween;

  # Sanity checks, to look for dependencies/bias in the data
  inherit (callPackage ./stability.nix {
            inherit sampledBenchmarkData;
          })
    plotTests stabilityPlots;
};

# Force tests to run *before* we expose this stuff to Nix; otherwise we might
# spend ages generating data, which then gets mangled by some trivial error
assert all (test: import "${test}") [ plotTests ];
{
  inherit stabilityPlots;
}
