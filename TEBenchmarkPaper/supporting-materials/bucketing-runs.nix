{ haskell-te-defs, lib, runCommand }:

with lib;
rec {
  sizes = [ 10 20 30 ];
  reps  = 30;

  samples = drawSamples sizes reps;

  bucketing-data = runCommand "not-implemented" {} ''
    echo "FIXME: bucketing-data" 1>&2
    exit 1
  '';

  bucketing-graph = runCommand "bucketing-graph.png"
    {
      data = bucketing-data;
    }
    ''
      echo "FIXME: No bucket graph maker" 1>&2
      exit 1
    '';
}
