# Supporting materials shared by abstract/ and slides/
{ callPackage, jq, latestGit, lib, racket, runCommand, writeScript }:
with builtins;
with lib;
rec {
  tex = callPackage ./tex.nix {};

  haskell-te =
    with rec {
      local = "/home/chris/Programming/haskell-te";
    };
    import (latestGit {
      url = if pathExists local
               then local
               else "http://chriswarbo.net/git/haskell-te.git";
    });

  samples = haskell-te.drawSamples {
    sizes = range 5 19;
    reps  = 30;
  };

  runtimes = with rec {
    sizes = attrNames samples;
    names = attrNames samples."${head sizes}".averageTimes;
  };
  genAttrs names (name: map (size: runCommand "tagged-${name}-${size}"
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
