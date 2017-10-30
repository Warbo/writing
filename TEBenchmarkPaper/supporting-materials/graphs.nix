{ fail, fetchgit, gnuplot, jq, miller, mkBin, runCommand, wrap }:

with builtins;
with rec {
  repo = trace "FIXME: Use repo not path" /home/chris/Programming/haskell-te;

  data = runCommand "data.json"
    {
      inherit repo;
      buildInputs = [ jq ];
      pth = trace "FIXME: Pick real commit" ".asv/results/nixos/9c7d0eaa-nix-py-dirnull.json";
    }
    ''
      set -e
      jq '.' < "$repo/$pth" > "$out"
    '';

  mean = mkBin {
    name = "mean";
    paths = [ miller ];
    script = trace "Ratio of averages or average of ratios?" ''
      #!/usr/bin/env bash
      set -e
      mlr --ocsv --headerless-csv-output stats1 -f 1 -a mean
    '';
  };

  median = mkBin {
    name = "median";
    paths = [ miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      mlr --ocsv --headerless-csv-output stats1 -f 1 -a p50
    '';
  };

  timePlot = wrap {
    name   = "timePlot";
    paths  = [ fail gnuplot miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$1" ]] || fail "No arg given"
      [[ -e "$1" ]] || fail "No such file '$1'"

      #echo "set terminal epslatex size 8.89cm,6.65cm color colortext
      #      set output 'times.tex'
      echo "set terminal pngcairo size 350,262 enhanced font 'Verdana,10'
            plot '$1'" | gnuplot
    '';
  };

  quickspecData = runCommand "quickspecData"
    {
      inherit data timePlot;
      buildInputs = [ jq mean median miller ];
    }
    ''
      #!/usr/bin/env bash
      set -e
      PRE='.results | ."quickspectip.track_data" | .result | .[0]'
      jq -r "$PRE | keys | .[]" < "$data" | while read -r SIZE
      do
        PRE2="$PRE | .[\"$SIZE\"] | .reps"
        T=$(jq -r "$PRE2 | .[] | .time" < "$data" | median)
        echo -e "$SIZE\t$T" >> times.dat

        P=$(jq -r "$PRE2 | .[] | .precision | if . == null then 0 else if . == [] then 0 else . end end" < "$data" | mean)
        echo "PRECISION: $P" 1>&2
        echo -e "$SIZE\t$P" >> precision.dat

        R=$(jq -r "$PRE2 | .[] | .recall | if . == null then 0 else . end" < "$data" | mean)
        echo "RECALL: $R" 1>&2
        echo -e "$SIZE\t$R" >> recall.dat
      done

      mkdir "$out"
      "$timePlot" times.dat > "$out/times.png"
      "$timePlot" precision.dat > "$out/precision.png"
      "$timePlot" recall.dat > "$out/recall.png"
    '';
};
quickspecData
