{}:

rec {
  getData = cmd: precisionRecallOfData (pkgs.stdenv.mkDerivation {
    # Forces tests to be run before we spend ages getting the data
    inherit plotTests;
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te jq ];
    SKIP_DATA    = getEnv "SKIP_DATA";
    buildCommand = ''
      if [[ -n "$SKIP_DATA" ]]
      then
        for S in 5 10 15 100
        do
          jq -n --arg info "$S" \
             '{"cmd":"${cmd}","info":$info, "results":[{
               "failure":null, "time": 1.23, "stdout": "/dev/null",
               "stderr": "/dev/null"
              }]}'
        done | jq -s '.' > "$out"
      else
        ${explorationOptions}
        SAMPLE_SIZES="5 10 15 100" ${cmd} | jq -s '.' > "$out"
      fi
    '';
  });

  explorationOptions = ''
    export        JVM_OPTS="-Xmx168m -Xms168m -Xss1m"
    export EXPLORATION_MEM=3000000
    export        MAX_SECS=120
    export            REPS=30
  '';

  smallTheoryData = cmd:
    with rec {
      data = stdenv.mkDerivation {
        name         = "${cmd}-small-theory-data";
        hte          = haskell-te-src;
        SKIP_DATA    = getEnv "SKIP_DATA";
        buildInputs  = [ haskell-te jq ];
        buildCommand = ''
          ${explorationOptions}
          for B in "$hte"/benchmarks/*.smt2
          do
            NAME=$(basename "$B" .smt2)
            mkdir -p "$out"
            if [[ -n "$SKIP_DATA" ]]
            then
              echo '[{"cmd":"${cmd}","info":"dummy data","results":[
                      {"time":    1.23,
                       "failure": null,
                       "stdin":   "/dev/null",
                       "stdout":  "/dev/null",
                       "stderr":  "/dev/null"}
                    ]}]' > "$out/$NAME.json"
            else
              ${cmd} < "$B"| jq -s '.' > "$out/$NAME.json"
            fi
          done
        '';
      };
    };
    stdenv.mkDerivation {
      inherit data;
      name         = "small-theory-precision-recall";
      buildInputs  = [ haskell-te-defs.tipBenchmarks.tools jq ];
      buildCommand = ''
        function stripMsgs {
          grep -v "^Depth" < "$1" || echo ""
        }

        for F in "$data"/*.json
        do
          mkdir -p "$out"
          NAME=$(basename "$F" .json)

          echo "Looking for ground truth equations for '$NAME'" 1>&2
          EQS_FILE="${./isabelle-theorems}/$NAME.smt2"
          [[ -f "$EQS_FILE" ]] || {
            echo "No such file '$EQS_FILE'" 1>&2
            exit 1
          }

          echo "Looping through benchmark executions" 1>&2
          while read -r EXECUTION
          do
            echo "Looping through benchmark iterations" 1>&2
            while read -r ITERATION
            do
              echo "Extracting equations found by this iteration" 1>&2
              STDOUT=$(echo "$ITERATION" | jq -r '.stdout')
              EQUATIONS=$(stripMsgs "$STDOUT" | jq -s '.')

              echo "Comparing equations to ground truth" 1>&2
              WANTED=$(echo "$EQUATIONS" |
                       GROUND_TRUTH="$EQS_FILE" \
                       TRUTH_SOURCE="$EQS_FILE" precision_recall_eqs)

              echo "Annotating the iteration with these results" 1>&2
              echo "$ITERATION" | jq --argfile wanted <(echo "$WANTED") \
                                     '. + $wanted'
            done < <(echo "$EXECUTION" | jq -c '.results | .[]') |
              jq -s --argfile execution <(echo "$EXECUTION") \
                 '$execution + {"results": .}'
          done < <(jq -c '.[]' < "$F") | jq -s '.' > "$out/$NAME.json"
        done
      '';
    };
}
