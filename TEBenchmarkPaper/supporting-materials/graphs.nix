{ fail, fetchgit, jq, lzip, mkBin, perl, python, R, rPackages, runCommand,
  teBenchmark, tetex, tex, textWidth, which, wrap, writeScript }:

with builtins;
rec {
  haskell-te-src = fetchgit {
    url    = http://chriswarbo.net/git/haskell-te.git;
    rev    = "3c15e23";
    sha256 = "1y9ak8qwwa5g7ha2n2d26rbavgcv3y19s6qkk127wc0dip70z806";
  };

  normaliseData = name: repo: key: resultPaths: runCommand
    "normalised-${name}.json"
    {
      inherit key repo;
      buildInputs = [ jq lzip python ];
      files       = builtins.toJSON resultPaths;
      script      = writeScript "normalise.py" ''
        #!/usr/bin/env python
        import json
        import sys

        data = json.loads(sys.stdin.read())
        assert type(data) == type({}), repr({
          'error' : 'Stdin should be JSON object',
          'type'  : type(data)
        })

        for size in data:
          # Unwrap useless 'reps' wrapper
          if 'reps' in data[size]:
            data[size] = data[size]['reps']

          # Keep track of the samples we've already seen
          seenSamples = []

          for rep in sorted(data[size].keys()):
            # Remove more unnecessary wrappers
            for key in ['result', 'analysis']:
              if key in data[size][rep]:
                data[size][rep] = dict(  data[size][rep],
                                       **data[size][rep][key])
                del(data[size][rep][key])

            # These are inverse, so just use one
            if 'killed' in data[size][rep] and 'success' not in data[size][rep]:
              data[size][rep]['success'] = not data[size][rep]['killed']
            if 'killed' in data[size][rep]:
              del(data[size][rep]['killed'])

            # If IsaCoSy gets interrupted, that indicates it died from OOM
            stderr = data[size][rep]['stderr']
            if stderr is not None:
              interr = 'unable to increase stack'.replace(' ', "").lower()
              stderr = stderr.replace('\n',  ' ').replace(' ', "").lower()
              if interr in stderr:
                sys.stderr.write(repr({
                  'warning' : 'Exploration was interrupted',
                  'size'    : size,
                  'rep'     : rep
                }))
                data[size][rep]['success'] = False

            # We should always analyse, so this is useless
            if 'analysed' in data[size][rep]:
              assert data[size][rep]['analysed'], 'Run was not analysed'
              del(data[size][rep]['analysed'])

            # Remove some unneeded values, if present
            for key in ['runner', 'analyser',  # For provenance
                        'stdout', 'stderr',    # For debugging
                        'size',   'rep']:      # Violate "Once and Only Once"
              if key in data[size][rep]:
                del(data[size][rep][key])

            # Unwrap found and make comparable
            data[size][rep]['found'] = data[size][rep]['found'][0] \
                                       if data[size][rep]['success'] else []

            # Samples should be sets
            rawSample = data[size][rep]['sample']
            sampleSet = frozenset(rawSample)
            assert len(rawSample) == int(size), repr({
              'error'     : 'Wrong number of names sampled',
              'rep'       : rep,
              'size'      : size,
              'rawSample' : rawSample,
              'sampleSet' : sampleSet
            })

            assert len(sampleSet) == len(rawSample), repr({
              'error'     : 'Sampled names contain duplicates',
              'rep'       : rep,
              'size'      : size,
              'rawSample' : rawSample,
              'sampleSet' : sampleSet
            })

            # Remove this result if the sample has been seen before
            if sampleSet in seenSamples:
              sys.stderr.write(
                'Skipping dupe rep {} of size {}\n'.format(rep, size))
              del(data[size][rep])
            seenSamples += [sampleSet]

        print(json.dumps(data))
      '';
    }
    ''
      # Combine all files together
      while read -r F
      do
        echo "Processing '$F'" 1>&2
        if [[ -e input.json ]]
        then
          jq -n --slurpfile first  input.json              \
                --slurpfile second <(lzip -d < "$repo/$F") \
                --arg key "$key"                     \
            '($first  | .[0]) +
             ($second | .[0] | .results | .[$key] | .result | .[0])' > temp.json
          mv temp.json input.json
        else
          lzip -d < "$repo/$F" | jq --arg key "$key" \
            '.results | .[$key] | .result | .[0]' > input.json
        fi
      done < <(echo "$files" | jq -r '.[]')

      # Perform normalisation
      jq -e 'type | . == "object"' < input.json > /dev/null
      "$script" < input.json > "$out"
    '';

  isacosyData = normaliseData "isacosy"
    (fetchgit {
      url    = http://chriswarbo.net/git/isaplanner-tip.git;
      rev    = "1db28e7";
      sha256 = "0iarxsxl2pq5w4mv7y34anpzdvbzm8rsfkmdxlb49d1k5gkkc62w";
    })
    "benchmarks.track_data"
    [ "results/13dd39d1-nix-py-dirnull.json.lz"
      "results/08d9091f-nix-py-dirnull.json.lz" ];

  quickspecData = normaliseData "quickspec"
    haskell-te-src
    "quickspectip.track_data"
    [ "benchmarks/results/desktop/b1247807-nix-py-dirnull.json.lz"
      "benchmarks/results/desktop/bdea634a-nix-py-dirnull.json.lz" ];

  comparisonData = runCommand "benchmark-comparison-data"
    {
      inherit isacosyData quickspecData;
      buildInputs = [ jq lzip ];
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
      while read -r SIZE
      do
        echo "" 1>&2
        printf "Comparing runs of size $SIZE" 1>&2
        mkdir "$out/times_$SIZE"
        #echo "rep,quickspec,isacosy" > "$out/times_$SIZE.csv"

        CONF="$out/times_$SIZE/config.csv"
        echo "Name,Sample1,Sample2,ConfLevel,Coef" > "$CONF"

        while read -r REP
        do
          printf '.' 1>&2
          Q_TIME=$(echo "$Q_TIMES" | getTime "$SIZE" "$REP")
          I_TIME=$(echo "$I_TIMES" | getTime "$SIZE" "$REP")
          echo "$Q_TIME" > "$out/times_$SIZE/quickspec_$REP.csv"
          echo "$I_TIME" > "$out/times_$SIZE/isacosy_$REP.csv"
          printf '"%s","%s","%s",0.95,\n'              \
                 "rep$REP"                             \
                 "$out/times_$SIZE/quickspec_$REP.csv" \
                 "$out/times_$SIZE/isacosy_$REP.csv"   >> "$CONF"
          #echo "$REP,$Q_TIME,$I_TIME" >> "$out/times_$SIZE.csv"
        done < <(echo "$Q_TIMES" | jq -r --arg size "$SIZE" \
                                      '.[$size] | keys | .[]' | sort -n)
      done < <(sizes)
    '';

  compareTimes = runCommand "compare-times"
    {
      inherit comparisonData;
      buildInputs = [ R which ] ++ (with rPackages; [ coin ]);
      script      = ./compare.R;
      speedupSrc  = ./SpeedupTestTool.tar.bz2;
    }
    ''
      tar xf "$speedupSrc"
      TOOL="$PWD/SpeedupTest/SpeedUpTest.sh"

      mkdir "$out"
      for D in "$comparisonData"/times_*
      do
        SIZE=$(basename "$D" | grep -o '[0-9]*')
        mkdir "$out/times_$SIZE"
        pushd "$out/times_$SIZE" > /dev/null
          cp "$D/config.csv" ./config.csv
          echo "Config for size $SIZE" 1>&2
          cat ./config.csv 1>&2
          "$TOOL" config.csv || {
            echo "config.csv follows..."
            cat config.csv
            echo "config.csv follows..."
            cat config.csv.error
            exit 1
          } 1>&2
        popd > /dev/null
        #Rscript --vanilla "$script" < "$F" > "$out/times_$SIZE"
      done
    '';

  teTools = (import "${haskell-te-src}/nix-support" {}).tipBenchmarks.tools;

  tetex-hack = runCommand "tetex-hack"
    {
      inherit tetex;
      newDvipng = mkBin {
        name   = "dvipng";
        paths  = [ perl tetex ];
        script = ''
          #!/usr/bin/env bash
          set -e
          if [[ "x$1" = "x-version" ]]
          then
            dvipng "$@" | perl -pe 's/[^[:ascii:]]//g'
          else
            dvipng "$@"
          fi
        '';
      };
    }
    ''
      set -e

      # Hack for https://github.com/matplotlib/matplotlib/issues/4545/
      mkdir -p "$out/bin"
      for F in "$tetex/bin"/*
      do
        cp -s "$F" "$out/bin"/
      done
      rm "$out/bin/dvipng"
      ln -s "$newDvipng/bin/dvipng" "$out/bin/dvipng"
    '';

  # The dimensions of each graph, in units of textWidth; i.e. a width of 1.0
  # takes up the whole text width, whilst a height of 1.0 takes up a vertical
  # space equal to the page width.
  graphDims = {
    timeWidthFraction     = "1.0";
    timeHeightFraction    = "0.6";
    precRecWidthFraction  = "1.0";
    precRecHeightFraction = "0.8";
  };

  graphs = runCommand "quickspecGraphs"
    {
      inherit isacosyData quickspecData;
      buildInputs = [ lzip ];
      script      = wrap {
        name  =  "mkBenchmarkGraphs.py";
        file  = ./mkBenchmarkGraphs.py;
        vars  = graphDims // { inherit textWidth; };
        paths = [
          (python.withPackages (p: [ p.matplotlib p.numpy p.seaborn ]))
          tetex-hack
          tex
        ];
      };
    }
    ''
      set -e

      # Run script; it handles any even/odd split itself
      mkdir "$out"
      cd "$out"
      "$script" 1>&2
    '';
}
