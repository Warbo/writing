{ fail, fetchgit, gnuplot, jq, miller, mkBin, runCommand, wrap, writeScript }:

with builtins;
with rec {
  repo = fetchgit {
    url    = http://chriswarbo.net/git/haskell-te.git;
    rev    = "6855a50";
    sha256 = "0zgq3g3y23sjy0vi0dc263bavj795aj3kbydi2qchfcrv3dr6i4n";
  };

  data = runCommand "data.json.gz"
    {
      inherit repo;
      buildInputs = [ jq ];
      gzipped = "benchmarks/results/desktop/7a4cc07a-nix-py-dirnull.json.gz";
    }
    ''
      set -e
      cp "$repo/$gzipped" "$out"
    '';

  mean = mkBin {
    name   = "mean";
    paths  = [ miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      mlr --ocsv --headerless-csv-output stats1 -f 1 -a mean
    '';
  };

  median = mkBin {
    name   = "median";
    paths  = [ miller ];
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

  precRecPlot = wrap {
    name   = "precRecPlot";
    paths  = [ fail gnuplot miller ];
    vars   = {
      script = writeScript "precRec.gnuplot" ''
        set terminal pngcairo size 350,262 enhanced font 'Verdana,10'
        prec=system("echo $PREC")
        rec=system("echo $REC")
        plot prec title "Precision", \
             rec  title "Recall"
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$1" ]] || fail "No precision arg"
      [[ -e "$1" ]] || fail "No such file '$1'"
      [[ -n "$2" ]] || fail "No recall arg"
      [[ -e "$2" ]] || fail "No such file '$2'"

      PREC="$1" REC="$2" gnuplot < "$script"
    '';
  };

  quickspecGraphs = runCommand "quickspecGraphs"
    {
      inherit precRecPlot quickspecData timePlot;
      buildInputs = [ mean median miller ];
    }
    ''
      for FIELD in time prec rec
      do
        for S in "$quickspecData/$FIELD"/*
        do
          SIZE=$(basename "$S")
          if [[ "x$FIELD" = "xtime" ]]
          then
            VAL=$(median < "$S")
          else
            VAL=$(mean   < "$S")
          fi
          echo -e "$SIZE\t$VAL" >> "$FIELD.dat"
        done
      done

      mkdir "$out"
      "$timePlot"    time.dat         > "$out/time.png"
      "$precRecPlot" prec.dat rec.dat > "$out/precRec.png"
    '';

  quickspecData = runCommand "quickspecData"
    {
      buildInputs = [ jq ];
      zipped      = data;
    }
    ''
      #!/usr/bin/env bash
      set -e
      PRE='.results | ."quickspectip.track_data" | .result | .[0]'
      gunzip < "$zipped" > ./data

      mkdir -p "$out/time"
      mkdir -p "$out/prec"
      mkdir -p "$out/rec"

      jq -r "$PRE | keys | .[]" < ./data | while read -r SIZE
      do
        echo "Extracting data for size $SIZE" 1>&2
        PRE2="$PRE | .[\"$SIZE\"] | .reps"
        jq -r "$PRE2 | .[] | .time" < ./data > "$out/time/$SIZE"

        jq -r "$PRE2 | .[] | .precision |
               if . == null
                  then 0
                  else if . == []
                          then 0
                          else .
                       end
               end" < ./data > "$out/prec/$SIZE"

        jq -r "$PRE2 | .[] | .recall |
               if . == null then 0 else . end" < ./data > "$out/rec/$SIZE"
      done
    '';
};
quickspecGraphs
