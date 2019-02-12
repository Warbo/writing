# Supporting materials shared by abstract/ and slides/
{ callPackage, fetchgit, jq, lib, pandocPkgs, racket, runCommand, writeScript }:
with builtins;
with lib;
rec {
  tex = callPackage ./tex.nix {};

  renderers = [ pandocPkgs tex ];

  haskell-te = import (fetchgit {
    url    = "http://chriswarbo.net/git/haskell-te.git";
    rev    = "75d4b50";
    sha256 = "1ix03qxiif9cjxqa6v31ffzwi4cfbd5lp6axfxaidljmhrzycw4n";
  });

  samples =
    with {
      dataJSON = getEnv "DATA_JSON";
    };
    if dataJSON == ""
       then haskell-te.resultsFor {
              sizes = range 5 19;
              reps  = 30;
            }
       else trace "Taking data from DATA_JSON file ${dataJSON}"
                  haskell-te.analyseData (fromJSON (readFile dataJSON));

  prepareAllEqs =
    with rec {
      eqs = mapAttrs (size: map (iteration: writeScript
              "found-${size}-${iteration.rep}"
              (toJSON {
                inherit size;
                inherit (iteration) names rep;
                stdout = iteration.outputs.quickSpec.stdout;
              })))
            samples.iterations;
    };
    runCommand "prepare-eqs"
    {
      FOUND = attrValues eqs;
      buildInputs = [ jq ];
    }
    ''
      function strip {
        grep '^{' || echo ""
      }

      for F in $FOUND
      do
        jq -r '.stdout' < "$F" | strip | jq -s '.'             > sout
        jq -r '.names'  < "$F" | sed 's/\\n/\n/g' | jq -sR '.' > names
        jq --argfile sout sout --argfile names names \
           '. + {"stdout": $sout, "names": $names}' < "$F"
      done | jq -s '.' > "$out"
    '';

  processedEqs = runCommand "processed"
    {
      inherit prepareAllEqs;
      buildInputs = [ haskell-te.tipBenchmarks.tools ];
      extract = ./extractEqs.rkt;
    }
    ''
      D_LOC=$(command -v defs)
          D=$(cat "$D_LOC" | grep -o '/nix/store/.*\.defs-wrapped')
        RKT=$(cat "$D_LOC" | grep "^export" | grep PATH |
              grep -o "/nix/store/.*tip-bench-env/bin")

      BENCHMARKS_FALLBACK=$(cat "$D_LOC" | grep "^export" |
                            grep BENCHMARKS_FALLBACK |
                            grep -o "/nix/store/.*tip-benchmarks")
      export BENCHMARKS_FALLBACK

      DEFS_LOCATION=$(grep -o '/nix/store/.*/defs\.rkt' < "$D")
      export DEFS_LOCATION

      echo "Processing equations from $prepareAllEqs" 1>&2
      "$RKT/racket" -f <(sed -e 's@DEFS_LOCATION@'"$DEFS_LOCATION"'@' < "$extract") \
             < "$prepareAllEqs" > "$out"
    '';

  qualityPlot = runCommand "quality.svg"
    {
      buildInputs = [ racket ];
      equations   = processedEqs;
    }
    ''
      racket "${./eqplot.rkt}" < "$equations" 1>&2
      exit 1
      cp *.svg "$out"
    '';

  runtimes =
    with rec {
      tools = attrNames samples.averageTimes;
      sizes = attrNames samples.averageTimes."${head tools}";
    };
    genAttrs tools
             (tool: map (size: runCommand "tagged-${tool}-${size}"
                          {
                            inherit size tool;
                            times = samples.averageTimes."${tool}"."${size}";
                            buildInputs = [ jq ];
                          }
                          ''
                            jq --argjson size "$size"             \
                               --arg     tool "$tool"             \
                               '. + {"tool":$tool, "size":$size}' \
                               < "$times" > "$out"
                          '')
                        sizes);

  runtimePlot = runCommand "runtimes.svg"
    {
      buildInputs = [ racket ];
      runtimes = writeScript "runtimes.json" (toJSON runtimes);
    }
    ''
      racket "${./runtimeplot.rkt}" < "$runtimes"
      cp *.svg "$out"
    '';
}
