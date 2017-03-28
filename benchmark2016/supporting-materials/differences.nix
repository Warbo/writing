{ jq, lib, makeWrapper, sampledBenchmarkData, sampledTestData, racket,
  runCommand, stdenv, writeScript }:

with builtins;
with lib;
rec {
  diffBetween = writeScript "diffBetween" ''
    #!/usr/bin/env bash

    # Takes 2 files, each should be a column of numbers. Outputs the pairwise
    # differences.
    paste "$1" "$2" | awk '{ print ($1 - $2) }'
  '';

  # Takes 2 files, set1 and set2, each containing a JSON object of the form:
  #
  #   {name1: [time1, time2, ...], name2: [time1, time2, ...], ...}
  #
  # Returns a JSON file of the form:
  #
  # {name1: [set1.name1[0] - set2.name1[0], set1.name1[1] - set2.name1[1], ...],
  #  name2: [set1.name2[0] - set2.name2[0], set1.name2[1] - set2.name2[1], ...],
  #  ...}
  diffsBetween = set1: set2: runCommand "diffs"
    { inherit set1 set2; buildInputs = [ jq ]; }
    ''
      set -e
      set -o pipefail

      function keyFrom() {
        jq -r --arg k "$1" '.[$k] | .[]' < "$2"
      }

      # Loop through set1's keys
      while read -r KEY
      do
        # Look up $KEY in set1 and set2, diff them, collect the results in a
        # key/value pair, so that from_entries can construct an object outside
        # the loop
        ${diffBetween} <(keyFrom "$KEY" "$set1") <(keyFrom "$KEY" "$set2") |
          jq -s --arg k "$KEY" '{"key": $k, "value": .}'
      done < <(jq -r 'keys | .[]' < "$set1") | jq -s '. | from_entries' > "$out"
    '';

  # Pulls out times from JSON results
  rawTimesOf = data: runCommand "raw-times"
    { inherit data; buildInputs = [ jq ]; }
    ''
      jq 'map(. as $entry | {"key":   .info,
                             "value": (.results |
                                       map(if .failure == 143
                                              then $entry.timeout
                                              else .time
                                           end | tostring))}) |
          from_entries' < "$data" > "$out"
    '';

  rawTimes = mapAttrs (name: data: rawTimesOf data);

  timeDifferences = data:
    with rec {
      times = rawTimes data;

      names = attrNames times;

      diffs = name: genAttrs (filter (n: n != name) names)
                             (n: diffsBetween times."${name}" times."${n}");
    };
    genAttrs names diffs;

  diffPlot = data: runCommand "diffPlot"
    {
      buildInputs = [ racket ];
      data        = writeScript "data.json" (toJSON data);
      diffPlot    = ./diffPlot.rkt;
    }
    ''
      racket "$diffPlot" < "$data" #> "$out"
    '';

  diffPlots = data:
    with rec {
      diffs = timeDifferences data;
    };
    diffPlot diffs.quickspecBench;

  testDiffPlots = diffPlots sampledTestData;

  benchmarkDiffPlots = diffPlots sampledBenchmarkData;
}
