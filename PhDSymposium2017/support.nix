# Supporting materials shared by abstract/ and slides/
{ callPackage, jq, latestGit, lib, racket, runCommand, writeScript }:
with builtins;
with lib;
rec {
  tex = callPackage ./tex.nix {};

  haskell-te =
    with rec {
      local = /home/chris/Programming/haskell-te;
    };
    import (if pathExists local
               then local
               else latestGit {
                      url = "http://chriswarbo.net/git/haskell-te.git";
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

  data = runtimes;
}
