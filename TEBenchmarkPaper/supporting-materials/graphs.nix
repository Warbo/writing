{ fail, fetchgit, jq, lzip, mkBin, perl, python, runCommand, teBenchmark, tetex,
  tex, textWidth, wrap, writeScript }:

with builtins;
rec {
  repo = fetchgit {
    url    = http://chriswarbo.net/git/haskell-te.git;
    rev    = "be30d74";
    sha256 = "0skmiy0riry3jxkz6pk3lf38bqd3lw6gxlh4l6j41ccdm7lwlh55";
  };

  data = runCommand "data.json.lz"
    {
      inherit repo;
      buildInputs = [ jq ];
      lzipped = "benchmarks/results/desktop/b1247807-nix-py-dirnull.json.lz";
    }
    ''
      set -e
      ln -s "$repo/$lzipped" "$out"
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
      inherit data;
      buildInputs = [ lzip ];
      script      = wrap {
        name  =  "mkQuickSpecGraphs.py";
        file  = ./mkQuickSpecGraphs.py;
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
      mkdir "$out"
      cd "$out"
      lzip -d < "$data" | "$script" 1>&2
    '';
}
