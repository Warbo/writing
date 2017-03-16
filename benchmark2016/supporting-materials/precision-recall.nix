{}:

rec {
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

  precisionRecallTable = stdenv.mkDerivation {
    name         = "precision-recall-table";
    data         = attrsToDirs small;
    buildInputs  = [ jq miller ];
    buildCommand = ''
      # Loop through each command
      for D in "$data"/*
      do
        pushd "$D"
        DNAME=$(basename "$D")
        echo "In $D" 1>&2
        find "$D" 1>&2
        mkdir -p "$out/$DNAME"

        # Loop through each JSON file
        for F in ./*
        do
          FNAME=$(basename "$F" .json)
          if echo "$F" | grep "\.json$" > /dev/null
          then
            # Might as well keep the JSON
            cp -r "$F" "$out/$DNAME/"

            # Loop through each iteration
            while read -r LINE
            do
              # Loop through the fields we want to analyse
              for FIELD in precision recall time
              do

                echo "FIXME: Should we be discarding divide-by-zero? Ask Jianguo" 1>&2

                # Collect up field values from 'results' into an array, discard
                # anything non-numeric, prepend the field name and print one
                # entry per line
                FIELD_DATA=$(echo "$LINE" |
                             jq -r --arg field "$FIELD" \
                                '.results | map(.[$field])                |
                                            map(select(type == "number")) |
                                            [$field] + .                  |
                                            .[]')

                # Take stats for this field
                echo "$FIELD_DATA" | mlr --icsv --ojson        \
                                         stats1 -a mean,stddev \
                                         -f "$FIELD"
              done | jq -s --slurpfile line <(echo "$LINE") \
                        'add | . + $line[0]'
            done < <(jq -c '.[]' < "$F") |
              jq -s '.' > "$out/$DNAME/$FNAME.precrec"
          fi
        done
        popd
      done
    '';
  };
}
