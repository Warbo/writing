rec {
  pkgs = import <nixpkgs> {};

  inherit (pkgs)
    buildEnv callPackage jq lib makeWrapper pythonPackages runCommand stdenv
    writeScript;

  inherit (lib)
    range stringToCharacters take toInt;

  inherit (callPackage ./drawStabilisePlots.nix {})
    chartsOf plotTests;

  haskell-te      = import haskell-te-src;
  haskell-te-defs = import "${haskell-te-src}/nix-support" {};
  haskell-te-src  = pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "6c784f0";
    sha256 = "0qsyy8vf49q9qwy4ai99dhrpi6n0bz5fmfa7mbm8pjlp84980fzl";
  };

  getData = cmd: precisionRecallOfData (pkgs.stdenv.mkDerivation {
    # Forces tests to be run before we spend ages getting the data
    inherit plotTests;
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      ${explorationOptions}
      SAMPLE_SIZES="5 10 15 100" ${cmd} | jq -s '.' > "$out"
    '';
  });

  explorationOptions = ''
    export        JVM_OPTS="-Xmx168m -Xms168m -Xss1m"
    export EXPLORATION_MEM=3000000
    export        MAX_SECS=600
    export            REPS=30
  '';

  smallTheoryData = cmd: precisionRecallOfData (stdenv.mkDerivation {
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

  precisionRecallOfData = data:
    stdenv.mkDerivation {
      name         = "precision-recall";
      src          = data;
      buildInputs  = [ haskell-te-defs.tipBenchmarks.tools jq ];
      unpackPhase  = "true"; # Nothing to do
      buildCommand = ''
        function stripMsgs {
          grep -v "^Depth" < "$1" || echo ""
        }

        function processFile {
          while read -r EXECUTION
          do
            SAMPLE_SIZE=$(echo "$EXECUTION" | jq -r '.info')
            echo "Analysing samples of size $SAMPLE_SIZE" 1>&2
            REP=0
            while read -r ITERATION
            do
              # Get the names used in this sample (choose_sample is deterministic)
              REP=$(( REP + 1 ))
              echo "Analysing iteration $REP" 1>&2

              echo "Obtaining the sample used by this iteration" 1>&2
              SAMPLED_NAMES=$(choose_sample "$SAMPLE_SIZE" "$REP")
              SAMPLED_JSON=$(echo "$SAMPLED_NAMES" | jq -R '.' | jq -s '.')
              export SAMPLED_NAMES

              echo "Extracting equations found by this iteration" 1>&2
              STDOUT=$(echo "$ITERATION" | jq -r '.stdout')
              EQUATIONS=$(stripMsgs "$STDOUT" | jq -s '.' | decode)

              echo "Fetching conjectures reachable from this sample" 1>&2
              WANTED=$(echo "$EQUATIONS" | conjectures_for_sample)

              echo "Annotating the iteration with these results" 1>&2
              echo "$ITERATION" | jq --argjson sample "$SAMPLED_JSON"   \
                                     --argfile wanted <(echo "$WANTED") \
                                     '. + {"sample"    : $sample} + $wanted'
            done < <(echo "$EXECUTION" | jq -c '.results | .[]') |
              jq -s --argfile execution <(echo "$EXECUTION") \
                 '$execution + {"results": .}'
          done < <(jq -c '.[] | .' < "$1") | jq -s '.'
        }

        if [[ -f "$src" ]]
        then
          processFile "$src" > "$out"
        else
          mkdir -p "$out"
          for F in "$src"/*
          do
            NAME=$(basename "$F")
            processFile "$F" > "$out/$NAME"
          done
        fi
      '';
    };

  quickSpec = rec {
    data  = getData "quickspecBench";
    small = smallTheoryData "quickspecBench";
  };

  mlSpec = rec {
    data  = getData "mlspecBench";
    small = smallTheoryData "mlspecBench";
  };

  getStats =
    with {
      script = writeScript "getStats.py" ''
        """Given a JSON array of numbers on stdin, returns mean and stddev."""
        import json
        import numpy as np

        data = json.loads(sys.stdin.read())
        print(json.dumps({"mean"   : np.mean(data),
                          "stddev" : np.stddev(data)}))
      '';
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "stats.py" { buildInputs = [ makeWrapper ]; } ''
      makeWrapper "${script}" "$out" --prefix PATH : "${env}/bin"
    '';

  precisionRecallTable = stdenv.mkDerivation {
    mlspec    = mlSpec.small;
    quickspec = quickSpec.small;

    name         = "precision-recall-table";
    buildInputs  = [ jq ];
    buildCommand = ''
      for F in "$mlspec"/*
      do
        NAME=$(basename "$F" .json)
        MLMEAN=$(jq ' ' < "$F")
      done
    '';
  };
}
