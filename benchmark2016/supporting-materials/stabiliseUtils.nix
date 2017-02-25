with builtins;
rec {
  defPkgs = import <nixpkgs> {};
  pkgs    = import (defPkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "16.09";
    sha256 = "1cx5cfsp4iiwq8921c15chn1mhjgzydvhdcmrvjmqzinxyz71bzh";
  }) { config = {}; };

  inherit (pkgs)
    buildEnv callPackage jq lib makeWrapper pythonPackages runCommand stdenv
    writeScript;

  inherit (lib)
    mapAttrs range stringToCharacters take toInt;

  inherit (callPackage ./drawStabilisePlots.nix {})
    plotsOf plotTests;

  haskell-te      = import haskell-te-src;
  haskell-te-defs = import "${haskell-te-src}/nix-support" {};
  haskell-te-src  = trace "FIXME: USE GITHUB NOT DISK" pkgs.fetchgit {
    url = /home/chris/Programming/haskell-te;
    rev = "542728d";
    sha256 = "1pg1vyvkdc3pfcskszhhhh6pp5l8z6n00gbwlfqfd3cd3ghk32sd";
  };
  /*pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "542728d";
    sha256 = "15p5738hpv9gqqr4lhwxqfjbcnld4i6skf7hz6mj2j25y99f2833";
  };*/

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
    export        MAX_SECS=600
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
          done < <(jq -c '.[]' < "$1") | jq -s '.'
        }

        if [[ -f "$src" ]]
        then
          processFile "$src" > "$out"
        else
          mkdir -p "$out"
          while read -r F
          do
            SUFF=$(dirname "$F" | sed -e "s@$src@@g")
            mkdir -p "$out/$SUFF"

            NAME=$(basename "$F")
            echo "Writing $F to $out/$SUFF/$NAME" 1>&2
            processFile "$F" > "$out/$SUFF/$NAME"
          done < <(find "$src" -name "*.json")
        fi
      '';
    };

  results =
    let go = cmd: let data = getData cmd; in {
          "data.json" = data;
          plots       = plotsOf cmd data;
          small       = smallTheoryData cmd;
        };
     in {
          quickSpec = go "quickspecBench";
          mlSpec    = go "mlspecBench";
          hashSpec  = go "hashspecBench";
        };

  attrsToDirs = attrs:
    with rec {
      names     = attrNames attrs;
      dataOf    = name: attrsToDirs attrs."${name}";
      nameToCmd = name: ''
        cp -r "${dataOf name}" "$out/${name}"
      '';
      commands  = concatStringsSep "\n" (map nameToCmd names);
    };
    if attrs ? builder
       then attrs
       else stdenv.mkDerivation {
              name = "collated-data";
              buildCommand = ''
                mkdir -p "$out"
                ${commands}
              '';
            };

  collated = attrsToDirs results;

  graphed = stdenv.mkDerivation {
    inherit collated;
    name = "graphed";
    buildInputs = [];
    buildCommand = ''
      cp -r "$collated" "$out"
      while read -r JSONFILE
      do
        SUFF=$(echo "$JSONFILE" | sed -e "s@$out@@g")
         DIR=$(dirname "$SUFF")
        NAME=$(basename "$JSONFILE" .json)
        mkdir -p "$out/$DIR/$NAME"
        pushd "$out/$DIR/$NAME"
          plot < "$JSONFILE"
        popd
      done < <(find "$out" -name "*.json")
    '';
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
    inherit collated;
    name         = "precision-recall-table";
    buildInputs  = [ jq ];
    buildCommand = ''
      for D in "$collated"/*
      do
        pushd "$D"
        DNAME=$(basename "$D")
        mkdir -p "$out/$DNAME"
        for F in ./*
        do
          FNAME=$(basename "$F")
          #MEAN=$(jq ' ' < data)
        done
        popd
      done
    '';
  };
}
