with builtins;
with rec {
  pkgs = import <nixpkgs> {};

  inherit (pkgs)
    buildEnv graphicsmagick jq lib makeWrapper pythonPackages runCommand stdenv
    writeScript;

  inherit (lib)
    range stringToCharacters take toInt;

  haskell-te = import (pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "06de48e";
    sha256 = "1zh2mnwwhli2zb0qd13pjh234sw45r1sh4r5mm6zp1xsnyq1f7pi";
  });

  getData = cmd: pkgs.stdenv.mkDerivation {
    # Forces tests to be run before we spend ages getting the data
    inherit plotTests;
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      SAMPLE_SIZES="5 10 15" REPS=30 ${cmd} | jq -s '.' > "$out"
    '';
  };

  quickSpec = rec {
    data = getData "quickspecBench";
  };

  mlSpec = rec {
    data = getData "mlspecBench";
  };

  barChart =
    with {
      plotter = pkgs.writeScript "bar.py" ''
        #!/usr/bin/env python
        import sys
        import matplotlib
        import numpy as np
        import matplotlib.pyplot as plt
        import json
        import random

        def time_of(r):
          return r["time"] if r["failure"] is None else 0

        def draw_bar(data, mode, size):
          N = len(data)
          x = range(N)

          plt.figure(figsize=(8, 3))
          plt.bar(x, data, width=1/1.5, color="blue", log=True)
          plt.title("Sample size %s, %s" % (size, mode))

          plt.savefig("bar-%s-%s.png" % (mode, size))

        def draw_bars(times, shuffled, index):
          # Write the ordered times
          draw_bar(times, "ordered", sizes[index])

          # Write the shuffled times
          draw_bar(shuffled, "shuffled", sizes[index])

        def lag_plot(lag, times, mode, index):
          plt.figure(figsize=(8, 8))
          plt.plot(times[lag:], times[:-1*lag], 'kx')
          plt.title("Lag %s, sample size %s, %s" % (lag, sizes[index], mode))

          plt.savefig("lag-%s-%s-%s.png" % (lag, mode, sizes[index]))

        def lag_plots(times, mode, index):
          for lag in [1,2,3,4]:
            lag_plot(lag, times, mode, index)

        # For each run of data, render an ordered figure and a shuffled figure
        data  = json.loads(sys.stdin.read())
        sizes = [r["info"] for r in data]
        for index, run in enumerate(data):
          sample_size = int(run["info"])
          times       = map(time_of, run["results"])

          # Shuffle a copy of the times. Use fixed seed for reproducibility.
          shuffled = [x for x in times]
          random.Random(42).shuffle(shuffled)

          draw_bars(times,    shuffled,   index)
          lag_plots(times,    "ordered",  index)
          lag_plots(shuffled, "shuffled", index)
      '';
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "bar.py" { buildInputs = [ makeWrapper ]; } ''
      makeWrapper "${plotter}" "$out" --prefix PATH : "${env}/bin"
    '';

    barChartOf = name: data:
      stdenv.mkDerivation {
        name         = "barchart-${name}";
        buildInputs  = [ graphicsmagick ];
        buildCommand = ''
          mkdir -p "$out"
          cd "$out"
          echo "Plotting bar charts for ${data}" 1>&2
          "${barChart}" < "${data}"
          for ORD in bar-ordered-*.png
          do
            SHUF=$(echo "$ORD" | sed -e 's/ordered/shuffled/g')
            COMB=$(echo "$ORD" | sed -e 's/ordered/combined/g')
            gm convert "$ORD" "$SHUF" -append "$COMB"
          done
        '';
      };

    plotsOf = name: data:
      pkgs.runCommand "stabilisePlotsOf-${name}"
        {
          inherit data;
          bars = barChartOf name data;
        }
        ''
          mkdir "$out"
          cp -rv "$data" "$out/data.json"
          cp -rv "$bars" "$out/bars"
        '';

    plotTests = stdenv.mkDerivation {
      name = "plot-tests";
      # Generate some semi-plausible data to test with
      src  =
        with rec {
          data = writeScript "test-data" (toJSON [corr uncorr]);
          corr = {
            info    = 1;
            results = map (n: {
                            time    = (2 * n) + 3;
                            failure = if elem n [3 8]
                                         then n + 20
                                         else null;
                          })
                          (range 1 30);
          };

          uncorr = {
            info    = 2;
            results = map (n: {
                            time    = randomise n;
                            failure = if elem n [3 8]
                                         then n + 20
                                         else null;
                          })
                          (range 1 30);
          };

          randomise = n:
            with rec {
              hash   = hashString "sha256" (toString n);
              digits = stringToCharacters "0123456789";
              valid  = filter (c: elem c digits) (stringToCharacters hash);
              prefix = take 4 (valid ++ digits);
            };
            toInt (concatStringsSep "" prefix);
        };
        plotsOf "test" data;

      doCheck    = true;
      checkPhase = ''
        echo "Testing plots from $src" 1>&2
        for MODE in ordered shuffled combined
        do
          for SET in $(seq 1 3)
          do
            [[ -f "$src/bars/bar-$MODE-$SET.png" ]] || {
              echo "Missing bar chart $MODE $SET" 1>&2
              exit 1
            }
          done
        done
      '';
    };
};

pkgs.runCommand "stabilisePlot"
  {
    quickSpecData = quickSpec.data;
       mlSpecData = mlSpec.data;
    quickSpecBars = barChartOf "quickSpec" quickSpec.data;
       mlSpecBars = barChartOf    "mlSpec"    mlSpec.data;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData" "$out/quickSpecData.json"
    cp -r    "$mlSpecData" "$out/mlSpecData.json"
    cp -r "$quickSpecBars" "$out/quickSpecStability.png"
    cp -r    "$mlSpecBars" "$out/mlSpecStability.png"
  ''
