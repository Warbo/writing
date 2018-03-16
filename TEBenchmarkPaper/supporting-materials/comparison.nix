{ fail, fetchurl, isacosyData, jq, nixListToBashArray, quickspecData, python3,
  R, replace, rPackages, runCommand, which, wrap, writeScript }:

rec {
  precRecData = runCommand "prec-rec-data"
    {
      inherit isacosyData quickspecData;
      buildInputs = [ jq ];
    }
    ''
      mkdir "$out"
      cd "$out"
      echo "Size,Rep,Generated,Wanted,Correct,Incorrect,Missed" |
        tee isacosy.csv > quickspec.csv

      function makeRows {
        jq -r '. as $all | keys | map(
                . as $size | $all[$size] | keys | map(
                  . as $rep | $all[$size][$rep] |
                    (.found  |                       length) as $gen     |
                    (.wanted |                       length) as $wanted  |
                    (.wanted | map(select(.found)) | length) as $correct |
                    [$size,
                     $rep,
                     ($gen                 | tostring),
                     ($wanted              | tostring),
                     ($correct             | tostring),
                     (($gen    - $correct) | tostring),
                     (($wanted - $correct) | tostring)] | join(",")) |
                join("\n")) |
              join("\n")'
      }

      function order {
        LC_ALL=C sort --field-separator=, -n -k 1,1 -k 2,2
      }

      makeRows < "$isacosyData"   | order >> isacosy.csv
      makeRows < "$quickspecData" | order >> quickspec.csv

      jq
    '';

  tabulatedPrecRec = runCommand "tabulated-prec-rec"
    {
      script = wrap {
        name   = "tabulate.py";
        paths  = [ (python3.withPackages (p: [ p.statsmodels ])) ];
        vars   = { inherit isacosyData quickspecData; };
        script = ''
          #!/usr/bin/env python3
          import sys
          msg = lambda x: sys.stderr.write(repr(x) + '\n')

          import os
          isacosyFile   = os.getenv('isacosyData'  )
          quickspecFile = os.getenv('quickspecData')

          import json
          isacosyData   = json.loads(open(isacosyFile,   'r').read())
          quickspecData = json.loads(open(quickspecFile, 'r').read())

          from statsmodels.sandbox.stats.runs import mcnemar

          totalICorrect   = 0
          totalIIncorrect = 0
          totalQCorrect   = 0
          totalQIncorrect = 0

          successICorrect   = 0
          successIIncorrect = 0
          successQCorrect   = 0
          successQIncorrect = 0

          totalIOnly = 0
          totalQOnly = 0
          totalBoth  = 0
          totalNone  = 0

          successIOnly = 0
          successQOnly = 0
          successBoth  = 0
          successNone  = 0

          sizes = sorted(list(set([size for size in isacosyData])))

          for size in sizes:
            iData = isacosyData[size]
            qData = quickspecData[size]

            # Get precision data: count up how many things we found and wanted

            generated = lambda repData: len(repData['found'])
            wanted    = lambda repData: len(repData['wanted'])
            correct   = lambda repData: len(list(filter(lambda eq: eq['found'],
                                                        repData['wanted'])))
            incorrect = lambda repData: generated(repData) - correct(repData)
            missed    = lambda repData:    wanted(repData) - correct(repData)

            iCorrect   = sum([  correct(iData[rep]) for rep in iData])
            iIncorrect = sum([incorrect(iData[rep]) for rep in iData])

            qCorrect   = sum([  correct(qData[rep]) for rep in qData])
            qIncorrect = sum([incorrect(qData[rep]) for rep in qData])

            totalICorrect   += iCorrect
            totalIIncorrect += iIncorrect
            totalQCorrect   += qCorrect
            totalQIncorrect += qIncorrect

            with open('prec_' + size + '.csv', 'w') as f:
              f.write('{},{}\n{},{}'.format(str(qCorrect), str(qIncorrect),
                                            str(iCorrect), str(iIncorrect)))

            success = lambda rep: iData[rep]['success'] and qData[rep]['success']

            successICorrect   += sum([  correct(iData[rep]) for rep in iData \
                                      if success(rep)])
            successIIncorrect += sum([incorrect(iData[rep]) for rep in iData \
                                      if success(rep)])
            successQCorrect   += sum([  correct(qData[rep]) for rep in qData \
                                      if success(rep)])
            successQIncorrect += sum([incorrect(qData[rep]) for rep in qData \
                                      if success(rep)])

            # Get recall data: go through each ground truth and count how many
            # entries were found by just IsaCoSy, just QuickSpec, both or none
            iOnly = 0
            qOnly = 0
            both  = 0
            none  = 0
            for rep in iData:
              iTruth = sorted([thm['file'] for thm in iData[rep]['wanted']])
              qTruth = sorted([thm['file'] for thm in qData[rep]['wanted']])

              assert iTruth == qTruth, repr({
                'error'  : 'Mismatched ground truths',
                'size'   : size,
                'rep'    : rep,
                'iTruth' : iTruth,
                'qTruth' : qTruth
              })
              for name in iTruth:
                i = [t for t in iData[rep]['wanted'] if t['file'] == name][0]
                q = [t for t in qData[rep]['wanted'] if t['file'] == name][0]
                if     i['found'] and     q['found']:
                  both  += 1
                  if iData[rep]['success'] and qData[rep]['success']:
                    successBoth  += 1

                if     i['found'] and not q['found']:
                  iOnly += 1
                  if iData[rep]['success'] and qData[rep]['success']:
                    successIOnly += 1

                if not i['found'] and     q['found']:
                  qOnly += 1
                  if iData[rep]['success'] and qData[rep]['success']:
                    successQOnly += 1

                if not i['found'] and not q['found']:
                  none  += 1
                  if iData[rep]['success'] and qData[rep]['success']:
                    successNone += 1

            totalIOnly += iOnly
            totalQOnly += qOnly
            totalBoth  += both
            totalNone  += none

            with open('rec_' + size + '.csv', 'w') as f:
              f.write(str(mcnemar([[both, iOnly], [qOnly, none]], exact=True)))

          with open('precisionSuccess.csv', 'w') as f:
            f.write('{},{}\n{},{}\n'.format(successICorrect, successIIncorrect,
                                            successQCorrect, successQIncorrect))

          with open('recall', 'w') as f:
            f.write(repr({
              'all': {
                'both' : totalBoth,
                'quickspec only' : totalQOnly,
                'isacosy only' : totalIOnly,
                'neither' : totalNone,
                'mcnemar' : mcnemar([[  totalBoth,   totalIOnly], [  totalQOnly,   totalNone]], exact=True)
              },
              'success': {
                'both': successBoth,
                'quickspec only': successQOnly,
                'isacosy only': successIOnly,
                'neither': successNone,
                'mcnemar' : mcnemar([[successBoth, successIOnly], [successQOnly, successNone]], exact=True)
              }
            }))
        '';
      };
    }
    ''
      mkdir "$out"
      cd "$out"
      "$script"
    '';

  qualityComparison = runCommand "quality-comparisons"
    {
      inherit tabulatedPrecRec;
      buildInputs = [ R rPackages.Exact ];
      prec = writeScript "totalPrecision.R" ''
        library(Exact)
        tbl <- as.matrix(read.csv('precisionSuccess.csv', header=FALSE))
        exact.test(tbl, alternative="two.sided", method='Boschloo',
                   cond.row=TRUE, model='binomial')
      '';
    }
    ''
      mkdir "$out"
      cd "$out"
      cp "$tabulatedPrecRec/recall"               ./
      cp "$tabulatedPrecRec/precisionSuccess.csv" ./
      R CMD BATCH --no-save --no-restore --slave "$prec" > prec
    '';

  timeData = runCommand "time-comparison-data"
    {
      inherit isacosyData quickspecData;
      buildInputs = [ jq ];
    }
    ''
      function rawSizes {
        jq -r 'keys | .[]' < "$quickspecData"
        jq -r 'keys | .[]' < "$isacosyData"
      }

      function sizes {
        rawSizes | sort -n -u
      }

      TO=$(jq -r '[.[] | .[] | .timeout] | .[0]' < "$quickspecData")

      function getTime {
        jq --arg size "$1" --arg rep "$2" --argjson to "$TO" -r \
           '.[$size] | .[$rep] | [.time, $to] | min'
      }

      Q_TIMES=$(jq 'map_values(map_values({"time": .time}))' < "$quickspecData")
      I_TIMES=$(jq 'map_values(map_values({"time": .time}))' < "$isacosyData"  )

      mkdir "$out"
      CONF="$out/times.csv"
      echo "Name,Sample1,Sample2,ConfLevel,Coef" > "$CONF"

      while read -r SIZE
      do
        echo "" 1>&2
        printf "Comparing runs of size $SIZE" 1>&2
        mkdir "$out/times_$SIZE"

        printf '"%s","%s","%s",0.95,\n'             \
               "size$SIZE"                      \
               "$out/times_$SIZE/isacosy.csv"   \
               "$out/times_$SIZE/quickspec.csv" >> "$CONF"

        while read -r REP
        do
          printf '.' 1>&2
          Q_TIME=$(echo "$Q_TIMES" | getTime "$SIZE" "$REP")
          I_TIME=$(echo "$I_TIMES" | getTime "$SIZE" "$REP")
          echo "$Q_TIME" >> "$out/times_$SIZE/quickspec.csv"
          echo "$I_TIME" >> "$out/times_$SIZE/isacosy.csv"
          #echo "$REP,$Q_TIME,$I_TIME" >> "$out/times_$SIZE.csv"
        done < <(echo "$Q_TIMES" | jq -r --arg size "$SIZE" \
                                      '.[$size] | keys | .[]' | sort -n)
      done < <(sizes)
    '';

  compareTimes =
    with nixListToBashArray {
      name = "REPLACEMENTS";
      args = [
        ''wilcox.test(data1, data2, alternative="greater")''
        ''wilcoxsign_test(data1 ~ data2, paired=TRUE,
                          distribution='exact', correct=FALSE,
                          alternative="greater",
                          zero.method = c('Pratt'))''

        ''if(is.na(wt$p.value)) {''
        ''write(sprintf("P VALUE %f\n", pvalue(wt)), file="p-values",append=TRUE)
          if(is.na(pvalue(wt))) {''

        ''if(kt$p.value <= alpha) {''
        ''write(sprintf("KT P VALUE %f, ALPHA %f\n", kt$p.value, alpha), file="p-values",append=TRUE)
          if(kt$p.value <= alpha) {''

        ''if(!failed) {''
        ''write(sprintf("FAILED? %d\n", failed), file="p-values",append=TRUE)
          if(!failed) {''

        ''wt$p.value''
        ''pvalue(wt)''
      ];
    };
    runCommand "compare-times"
      (env // {
        inherit timeData;
        buildInputs = [ R replace which ] ++ (with rPackages; [ coin ]);
        speedupSrc  = ./SpeedupTestTool.tar.bz2;
      })
      ''
        # Initialise our bash arrays
        ${code}

        tar xf "$speedupSrc"
        TOOL="$PWD/SpeedupTest/SpeedUpTest.sh"
        R="$PWD/SpeedupTest/SpeedUpTest.R"

        echo "Patching $R to use paired Wilcoxon test" 1>&2

        # 'coin' package is needed for more flexible wilcoxon function
        echo "library(coin)" >  temp
        cat  "$R"            >> temp
        mv temp "$R"

        replace "${"$" + "{REPLACEMENTS[@]}"}" < "$R" > temp
        mv temp "$R"

        mkdir "$out"
        cp -v "$R" "$out/SCRIPT.R"
        pushd "$out" > /dev/null
          cp "$timeData/times.csv" ./config.csv
          "$TOOL" config.csv --weight equal || {
            echo "config.csv follows..."
            cat   config.csv
            echo "config.csv follows..."
            cat   config.csv.error
            exit 1
          } 1>&2
        popd > /dev/null
      '';

  timeComparison = runCommand "time-comparison"
    {
      inherit compareTimes;
      buildInputs = [ fail ];
    }
    ''
      mkdir "$out"
      echo "Checking columns" 1>&2
      for PAIR in '1	Name' '6	SpeedupMedian' '7	IsMedianSignificant'
      do
         COLUMN=$(echo "$PAIR" | cut -f1)
        HEADING=$(echo "$PAIR" | cut -f2)
          FOUND=$(head -n1 < "$compareTimes"/config.csv.out |
                  cut -d ',' -f"$COLUMN")
        [[ "x$FOUND" = 'x"'"$HEADING"'"' ]] ||
          fail "Column '$COLUMN' was '$FOUND' not '$HEADING'"
      done

      echo 'Sample Size,Speedup' > "$out/speedups.csv"

      SIZES=$(grep -o 'size[0-9]*' < "$compareTimes"/config.csv.out |
              grep -o '[0-9]*'                                      |
              sort -n                                               )
      while read -r SIZE
      do
         LINE=$(grep "size$SIZE"'"' < "$compareTimes"/config.csv.out)
        SPEED=$(echo "$LINE" | cut -d ',' -f6)
        echo "$SIZE,$SPEED" >> "$out/speedups.csv"
      done < <(echo "$SIZES")

      echo "Checking table" 1>&2
      COUNT=$(wc -l < "$out/speedups.csv")
      [[ "$COUNT" -gt 5 ]] || fail "Only '$COUNT' lines in table"
    '';

}
