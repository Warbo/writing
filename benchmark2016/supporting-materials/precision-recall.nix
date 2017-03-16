{}:

rec {
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
