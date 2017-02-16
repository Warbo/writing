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
    rev    = "e7c3a63";
    sha256 = "1gbicp70pmys78ix9xhai317ran1psf25x4jzmv1dkxbg0rycgl4";
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

  chart =
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
          """Return the time taken by a benchmark; 0 if it failed."""
          return r["time"] if r["failure"] is None else 0

        def draw_bar(data, mode, size):
          """Draw a bar chart of `data`; `mode` and `size` are for labels."""
          N = len(data)
          x = range(N)
          plt.bar(x, data, width=1/1.5, color="blue", log=True)
          plt.title("Sample size %s, %s" % (size, mode))

        def draw_bars(times, shuffled, index):
          """Draw one bar chart for `times` and one for `shuffled`. Put next to
          each other for easy comparison."""
          plt.figure(figsize=(8, 6))

          # Write the ordered times
          plt.subplot(2, 1, 1)
          draw_bar(times, "ordered", sizes[index])

          # Write the shuffled times
          plt.subplot(2, 1, 2)
          draw_bar(shuffled, "shuffled", sizes[index])

          plt.savefig("bars-%s.png" % sizes[index])

        def lag_plot(lag, times, mode, index):
          """Draw a lag plots for the `times` series."""
          plt.plot(times[lag:], times[:-1*lag], 'kx')
          plt.title("Lag %s, sample size %s, %s" % (lag, sizes[index], mode))

        def lag_plots(times, shuffled, index):
          """Draw 4 lag plots for `times` and `shuffled`."""
          plt.figure(figsize=(12, 24))
          plot_num = 0
          for lag in [1,2,3,4]:
            plot_num += 1
            plt.subplot(4, 2, plot_num)
            lag_plot(lag, times, "ordered", index)

            plot_num += 1
            plt.subplot(4, 2, plot_num)
            lag_plot(lag, shuffled, "shuffled", index)
          plt.savefig("lag-%s.png" % sizes[index])

        def correlation(data, mode, index):
          """Plot the autocorrelation function for `data`."""

          # Lift any integers to floats, so division won't truncate
          float_data = map(float, data)

          # Normalise our data, ready for autocorrelation. Begin by subtracting
          # the mean, so that our data becomes centred about zero.
          centred_data = [x - np.mean(float_data) for x in float_data]

          # Shrink the data such that it has a unit norm: we calculate the norm
          # (`ord=1` for L1 norm, `ord=2` for L2 norm, etc.), then divide each
          # element by this value (or an appropriate epsilon, if the norm is 0).
          normed_data = np.divide(centred_data,
                                  max(np.linalg.norm(centred_data, ord=2),
                                      sys.float_info.epsilon))

          plt.acorr(normed_data,
                    maxlags=None, usevlines=True, normed=True, lw=2)

          plt.title(
            "Autocorrelation, sample size %s, %s" % (sizes[index], mode))

        def correlations(times, shuffled, index):
          """Plot autocorrelation for ordered and shuffled series."""
          plt.figure(figsize=(12, 3))

          axis = plt.subplot(1, 2, 1)
          axis.set_xbound(lower=-0.5)
          correlation(times, "ordered", index)

          axis = plt.subplot(1, 2, 2)
          axis.set_xbound(lower=-0.5)
          correlation(shuffled, "shuffled", index)
          plt.savefig("acorr-%s.png" % sizes[index])

        # For each run of data, render an ordered figure and a shuffled figure
        data  = json.loads(sys.stdin.read())
        sizes = [r["info"] for r in data]
        for index, run in enumerate(data):
          sample_size = int(run["info"])
          times       = map(time_of, run["results"])

          # Shuffle a copy of the times. Use fixed seed for reproducibility.
          shuffled = [x for x in times]
          random.Random(42).shuffle(shuffled)

          for f in (draw_bars, lag_plots, correlations):
            f(times, shuffled, index)
      '';
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "bar.py" { buildInputs = [ makeWrapper ]; } ''
      makeWrapper "${plotter}" "$out" --prefix PATH : "${env}/bin"
    '';

    chartsOf = name: data:
      stdenv.mkDerivation {
        name         = "barchart-${name}";
        buildInputs  = [ graphicsmagick ];
        buildCommand = ''
          mkdir -p "$out"
          cd "$out"
          echo "Plotting bar charts for ${data}" 1>&2
          "${chart}" < "${data}"
        '';
      };

    plotsOf = name: data:
      pkgs.runCommand "stabilisePlotsOf-${name}"
        {
          inherit data;
          charts = chartsOf name data;
        }
        ''
          mkdir "$out"
          cp -rv "$data"   "$out/data.json"
          cp -rv "$charts" "$out/charts"
        '';

    plotTests = stdenv.mkDerivation {
      name = "plot-tests";
      # Generate some semi-plausible data to test with
      src  =
        with rec {
          data = writeScript "test-data" (toJSON [correlated uniform]);
          correlated = {
            info    = 1;
            results = map (n: {
                            time    = (2 * n) + 3;
                            failure = if elem n [3 8]
                                         then n + 20
                                         else null;
                          })
                          (range 1 30);
          };

          uniform = {
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
              # Generate digits uniformly, by taking a hash and discarding a-f
              hash   = hashString "sha256" (toString n);
              digits = stringToCharacters "1234567890";
              valid  = filter (c: elem c digits) (stringToCharacters hash);
            };
            # Append digits, just in case we hit a purely alphabetical hash ;)
            toInt (concatStringsSep "" (take 5 (valid ++ digits)));
        };
        plotsOf "test" data;

      doCheck    = true;
      checkPhase = ''
        echo "Testing plots from $src" 1>&2
        for SET in 1 2
        do
          for F in bars lag acorr
          do
            [[ -f "$src/charts/$F-$SET.png" ]] || {
              echo "Missing $F charts for $SET" 1>&2
              exit 1
            }
          done
        done
      '';
      installPhase = ''
        echo "Pass" > "$out"
      '';
    };
};

pkgs.runCommand "stabilisePlot"
  {
    quickSpecData = quickSpec.data;
       mlSpecData = mlSpec.data;
    quickSpecBars = chartsOf "quickSpec" quickSpec.data;
       mlSpecBars = chartsOf    "mlSpec"    mlSpec.data;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData" "$out/quickSpecData.json"
    cp -r    "$mlSpecData" "$out/mlSpecData.json"
    cp -r "$quickSpecBars" "$out/quickSpecStability.png"
    cp -r    "$mlSpecBars" "$out/mlSpecStability.png"
  ''
