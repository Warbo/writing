{ bucketing, gnuplot, jq, lzip, msgpack-tools, rpl, runCommand, writeScript }:

with builtins;
rec {
  property-stats = runCommand "property-stats"
    {}
    ''
      echo "TODO"
      exit 1
    '';

  bounds = "${bucketingSrc}/experiment-results/89132d7/bucketBounds.json.lz";

  boundsGraph = runCommand "bounds-graph"
    {
      inherit bounds;
      buildInputs = [ gnuplot jq ];
      script = writeScript "bounds-graph.gnuplot" ''
        set terminal pngcairo enhanced font "arial,10" fontscale 1.0 size 600, 400
        set output 'hashed.png'
        set title "Bucketing Cost, Recurrent vs Pseudorandom"
        set xlabel "Number of Functions"
        set ylabel "Available Proportion of Ground Truth"
        set yrange [0:1]
        set ytics scale 0.1
        set xtics scale 1
        unset mxtics
        unset key

        # The actual plotting. The comment is a sentinel value that will get
        # replaced by our bash script.
        plot #PLOTHERE
    '';
    }
    ''
      echo "TODO"
      exit 1
    '';

  graphs = runCommand "bucketing-graphs"
    {
      buildInputs = [ gnuplot jq lzip msgpack-tools rpl ];
      data        = "${bucketingSrc
        }/experiment-results/89132d7/averageBucketProportions.msgpack.lz";
      extract     = ''
        to_entries | .[] | .key as $size | .value |
          to_entries | .[] | .key as $method | .value |
            to_entries | .[] | .key as $bucketCount | .value | .proportion |
              [$method,
               $size,
               $bucketCount,
               (.mean   | tostring),
               (.stddev | tostring)
               ] | join("\t")
             '';

      # For rpl bug https://bugs.debian.org/cgi-bin/bugreport.cgi?bug=852813
      LANG = "en_US.UTF-8";

      script = writeScript "bucketing-graph.gnuplot" ''
        set terminal pngcairo enhanced font "arial,10" fontscale 1.0 size 600, 400
        set output 'hashed.png'
        set title "Bucketing Cost, Recurrent vs Pseudorandom"
        set xlabel "Number of Functions"
        set ylabel "Available Proportion of Ground Truth"
        set yrange [0:1]
        set ytics scale 0.1
        set xtics scale 1
        unset mxtics
        unset key

        # The actual plotting. The comment is a sentinel value that will get
        # replaced by our bash script.
        plot #PLOTHERE
      '';
    }
    ''
      echo "Converting JSON to TSV rows" 1>&2
      lzip -d < "$data" | msgpack2json | jq -r "$extract" > rows.tsv

      echo "Finding methods" 1>&2
      METHODS=()
      while read -r METHOD
      do
        METHODS+=("$METHOD")
      done < <(cut -f1 < rows.tsv | sort -u)

      echo "Finding bucket counts" 1>&2
      # Use 'sort' to do two things: strip out dupes ('-u'), and put in
      # descending order ('-r') so that entry 0 is the largest (-n is numeric)
      BUCKETCOUNTS=()
      while read -r BUCKETCOUNT
      do
        BUCKETCOUNTS+=("$BUCKETCOUNT")
        MAXBUCKET="$BUCKETCOUNT"  # After the loop, this will be max bucket count
      done < <(cut -f3 < rows.tsv | sort -u -n)

      MINGREY=0
      MAXGREY=200
      GREYSTEP=$(( (MAXGREY - MINGREY) / MAXBUCKET ))
      echo "Using greyscale step $GREYSTEP (largest bucket is $MAXBUCKET)" 1>&2
      unset MAXBUCKET
      unset MINGREY

      echo "Extracting data" 1>&2
      PLOTS=()
      for METHOD in "''${METHODS[@]}"
      do
        # Recurrent is solid, hashed is dashed
        DASHTYPE=""
        [[ "x$METHOD" = "xhashed" ]] && DASHTYPE='dashtype "- "'
        for BUCKETCOUNT in "''${BUCKETCOUNTS[@]}"
        do
          F="bucketcount_''${BUCKETCOUNT}_method_''${METHOD}.tsv"

          GREY=$(( MAXGREY - (GREYSTEP * BUCKETCOUNT) ))
          HEX=$(printf '%02X' "$GREY")
          echo "GREY $GREY HEX $HEX"
          unset GREY

          PLOTS+=("${concatStringsSep " " [
                       ''\"$F\"''
                       ''using 1:2''
                       ''title \"$METHOD bucket count $BUCKETcount\"''
                       ''with lines''
                       ''$DASHTYPE''
                       ''linetype rgb \"#$HEX$HEX$HEX\"''
                   ]}")

          echo "Extracting bucket count $BUCKETCOUNT for method $METHOD" 1>&2
          grep "^$METHOD	[0-9]*	$BUCKETCOUNT	" < rows.tsv | cut -f 2,4,5 |
                                                             sort -n >> "$F"
        done
      done

      cp "$script" script.gnuplot
      SENTINEL=$(printf ', \\\n     #PLOTHERE')
      for PLOT in "''${PLOTS[@]}"
      do
        DEST=$(printf '%s%s' "$PLOT" "$SENTINEL")
        rpl -q '#PLOTHERE' "$DEST" script.gnuplot
      done
      rpl -q "$SENTINEL" "" script.gnuplot

      cat script.gnuplot
      gnuplot < script.gnuplot

      mkdir "$out"
      cp *.png "$out"
    '';
}
