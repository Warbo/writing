{ callPackage, jq, latestGit, lib, racket, runCommand, writeScript }:

with builtins;
with lib;
rec {
  tex = callPackage ../tex.nix {};

  haskell-te = import (latestGit {
    url = "/home/chris/Programming/haskell-te";
  });

  samples = haskell-te.drawSamples {
    sizes = map (n: n * 5) (range 1 5/*20*/);
    reps  = 5/*30*/;
  };

  runtimes = with rec {
    sizes = attrNames samples;
    names = attrNames samples."${head sizes}".averageTimes;
  };
  genAttrs names (name: map (size: runCommand "tagged"
                                     {
                                       inherit size;
                                       tool  = name;
                                       times = samples."${size}"
                                                      .averageTimes
                                                      ."${name}";
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
