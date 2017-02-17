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
    rev    = "d1a6da7";
    sha256 = "1hc5m2phay8zvyqws47bzbrjlc98hm98caiikgivwd9a6phzkpqc";
  };

  getData = cmd: setup: pkgs.stdenv.mkDerivation {
    # Forces tests to be run before we spend ages getting the data
    inherit plotTests;
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      ${setup}
      export EXPLORATION_MEM=3000000
      MAX_SECS=600 SAMPLE_SIZES="5 10 15 100" REPS=30 ${cmd} | jq -s '.' > "$out"
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
        done < <(jq -c '.[] | .' < "$src") | jq -s '.' > "$out"
      '';
    };

  quickSpec = rec {
    data = precisionRecallOfData (getData "quickspecBench" "");
  };

  mlSpec = rec {
    data = precisionRecallOfData (getData "mlspecBench" ''
      export JVM_OPTS="-Xmx168m -Xms168m -XX:PermSize=32m -XX:MaxPermSize=32m -Xss1m"
    '');
  };
}
