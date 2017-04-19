{ haskell-te, jq, lib, stdenv }:

with lib;
rec {

  ## This part deals with samples from the TIP benchmark suite

  # Runs a benchmark
  getData = type: options: cmd: stdenv.mkDerivation (options // {
    name         = "${cmd}-${type}-data";
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      ${cmd} | jq -s '. | map(. + {"timeout": ${options.MAX_SECS}})' > "$out"
    '';
  });

  # Results to use in analysis
  fullData = getData "stabilise" explorationOptions;

  # Only takes one sample and has shorter timeout, to test our pipeline
  testData = getData "test" (explorationOptions // {
    MAX_SECS     = "120";
    REPS         = "3";
    SAMPLE_SIZES = "10 20 50 100 150 200";
  });

  forEachTool = genAttrs [ "hashspecBench" "mlspecBench" "quickspecBench" ];

  sampledTestData = forEachTool testData;

  sampledBenchmarkData = forEachTool fullData;

  explorationOptions = {
    JVM_OPTS        = "-Xmx168m -Xms168m -Xss1m";
    EXPLORATION_MEM = "3000000";
    MAX_SECS        = "3600";
    REPS            = "30";
    SAMPLE_SIZES    = "5 10 15 100";
  };

  ## This part deals with small, known theories of Nats and Lists

  smallTheoryTestData = cmd: processSmallTheory (stdenv.mkDerivation {
    name         = "${cmd}-small-theory-data";
    hte          = haskell-te-src;
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      for B in "$hte"/benchmarks/*.smt2
      do
        NAME=$(basename "$B" .smt2)
        mkdir -p "$out"
        echo '[{"cmd":"${cmd}","info":"dummy data","results":[
                {"time":    1.23,
                "failure": null,
                "stdin":   "/dev/null",
                "stdout":  "/dev/null",
                "stderr":  "/dev/null"}
              ]}]' > "$out/$NAME.json"
      done
    '';
  });

  smallTheoryData = cmd: processSmallTheory (stdenv.mkDerivation {
    name         = "${cmd}-small-theory-data";
    hte          = haskell-te-src;
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      ${explorationOptions}
      for B in "$hte"/benchmarks/*.smt2
      do
        NAME=$(basename "$B" .smt2)
        mkdir -p "$out"
        ${cmd} < "$B"| jq -s '.' > "$out/$NAME.json"
      done
    '';
  });

  processSmallTheory = data: stdenv.mkDerivation {
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
