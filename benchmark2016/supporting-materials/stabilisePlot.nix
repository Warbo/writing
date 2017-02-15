with rec {
  pkgs = import <nixpkgs> {};

  inherit (pkgs)
    buildEnv jq makeWrapper pythonPackages runCommand stdenv writeScript;

  haskell-te = import (pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "06de48e";
    sha256 = "1zh2mnwwhli2zb0qd13pjh234sw45r1sh4r5mm6zp1xsnyq1f7pi";
  });

  getData = cmd: pkgs.stdenv.mkDerivation {
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te ];
    buildCommand = ''
      SAMPLE_SIZES="5 10 15" REPS=30 ${cmd} > "$out"
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
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        import json
        import io
        import random

        data = json.loads(sys.stdin.read())

        def time_of(r):
          return r["time"] if r["failure"] is None else 0

        def draw_fig(data, buf, title):
          N = len(data)
          x = range(N)

          plt.figure(figsize=(8, 3))
          plt.bar(x, data, width=1/1.5, color="blue", log=True)
          plt.title(title)

          plt.savefig(buf, format='png')
          buf.seek(0)
          return buf

        def draw_figs(times, shuffled, index):
          # Write the ordered times
          draw_fig(times, ordered[index],
                   "Ordered samples of size %s" % sizes[index])

          # Write the shuffled times
          draw_fig(shuffled, scrambled[index],
                   "Shuffled samples of size %s" % sizes[index])

        # For each run of data, render an ordered figure and a shuffled figure
        ordered   = [io.BytesIO() for x in data]
        scrambled = [io.BytesIO() for x in data]
        sizes     = [r["info"] for r in data]
        for index, run in enumerate(data):
          sample_size = int(run["info"])
          times       = map(time_of, run["results"])

          # Shuffle a copy of the times. Use fixed seed for reproducibility.
          shuffled = [x for x in times]
          random.Random(42).shuffle(shuffled)

          draw_figs(times, shuffled, index)

        # Combine plot images
        from PIL import Image

        def beside(im1, im2):
          w1, h1 = im1.size
          w2, h2 = im1.size
          result = Image.new("RGB", (w1+w2, max(h1,h2)))
          result.paste(im1, (0, 0))
          result.paste(im2, (w1,0))
          return result

        def above(im1, im2):
          w1, h1 = im1.size
          w2, h2 = im1.size
          result = Image.new("RGB", (max(w1,w2), h1+h2))
          result.paste(im1, (0, 0))
          result.paste(im2, (0,h1))
          return result

        ims    = map(lambda index: above(Image.open(ordered[index]),
                                         Image.open(scrambled[index])),
                     range(len(data)))
        result = reduce(beside, ims)

        map(lambda buf: buf.close(), ordered + scrambled)

        # Write out combined image
        result.save(sys.stdout, format="PNG")
      '';
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "bar.py" { buildInputs = [ makeWrapper ]; } ''
      makeWrapper "${plotter}" "$out" --prefix PATH : "${env}/bin"
    '';

    chartOf = name: data:
      stdenv.mkDerivation {
        name         = "barchart-${name}";
        buildInputs  = [ jq ];
        buildCommand = ''
          jq -s '.' < "${data}" | "${barChart}" > "$out"
        '';
      };
};

pkgs.runCommand "stabilisePlot"
  {
    quickSpecData  = quickSpec.data;
       mlSpecData  = mlSpec.data;
    quickSpecChart = chartOf "quickSpec" quickSpecData;
       mlSpecChart = chartOf    "mlSpec"    mlSpecData;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData"  "$out/quickSpecData.json"
    cp -r    "$mlSpecData"  "$out/mlSpecData.json"
    cp -r "$quickSpecChart" "$out/quickSpecStability.png"
    cp -r    "$mlSpecChart" "$out/mlSpecStability.png"
  ''
