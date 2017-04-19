{ haskell-te-defs, lib, runCommand }:

with lib;
rec {
  sizes = [ 10 20 30 ];
  reps  = 30;

  samples = drawSamples sizes reps;

  bucketing-data = abort "FIXME: bucketing-data";

  bucketing-graph = runCommand "bucketing-graph.png"
    {
      data = bucketing-data;
    }
    ''
      echo "FIXME: No bucket graph maker" 1>&2
      exit 1
    '';
}
