{ fail, fetchgit, jq, mkBin, perl, python, runCommand, teBenchmark, tetex, tex,
  textWidth, wrap, writeScript }:

with builtins;
rec {
  repo = fetchgit {
    url    = http://chriswarbo.net/git/haskell-te.git;
    rev    = "7dd5eb6";
    sha256 = "106afmnc15m6cswc0mrh09hx6c8gvp3d350vbqh934r7hxaa6983";
  };

  data = runCommand "data.json.gz"
    {
      inherit repo;
      buildInputs = [ jq ];
      gzipped = "benchmarks/results/desktop/ce9c9478-nix-py-dirnull.json.gz";
    }
    ''
      set -e
      cp "$repo/$gzipped" "$out"
    '';

  teTools = (import "${repo}/nix-support" {}).tipBenchmarks.tools;

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
      script = wrap {
        name  =  "mkQuickSpecGraphs.py";
        file  = ./mkQuickSpecGraphs.py;
        paths = [
          (python.withPackages (p: [ p.matplotlib p.numpy p.seaborn ]))

          tetex-hack
          tex
        ];
        vars  = graphDims // {
          inherit textWidth;
          conjectures_for_sample = trace
            "FIXME: HaskellTE should do analysis even for failures"
            "${teTools}/bin/conjectures_for_sample";
          zipped = data;
        };
      };
    }
    ''
      set -e
      mkdir "$out"
      cd "$out"
      "$script" 1>&2
    '';
}
