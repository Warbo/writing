{ fail, fetchgit, gnuplot, jq, miller, mkBin, perl, python, render, runCommand,
  tetex, tex, wrap, writeScript }:

with builtins;
rec {
  data = runCommand "data.json.gz"
    {
      repo = fetchgit {
        url    = http://chriswarbo.net/git/haskell-te.git;
        rev    = "334d529";
        sha256 = "109g8hkpggjjlw7ksd7l157jknp4wkg9lbjlyiqqvqzah2kl65jf";
      };
      buildInputs = [ jq ];
      gzipped = "benchmarks/results/desktop/ce9c9478-nix-py-dirnull.json.gz";
    }
    ''
      set -e
      cp "$repo/$gzipped" "$out"
    '';

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

  mean = mkBin {
    name   = "mean";
    paths  = [ miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      mlr --ocsv --headerless-csv-output stats1 -f 1 -a mean
    '';
  };

  median = mkBin {
    name   = "median";
    paths  = [ miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      mlr --ocsv --headerless-csv-output stats1 -f 1 -a p50
    '';
  };

  precRecPlot = wrap {
    name   = "precRecPlot";
    paths  = [ fail gnuplot miller ];
    vars   = {
      script = writeScript "precRec.gnuplot" ''
        set terminal pngcairo size 350,262 enhanced font 'Verdana,10'
        prec=system("echo $PREC")
        rec=system("echo $REC")
        plot "prec.tsv" title "Precision", \
             "rec.tsv"  title "Recall"
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$PREC" ]] || fail "No precision arg"
      [[ -e "$PREC" ]] || fail "Can't find precisions '$PREC'"
      [[ -n "$REC"  ]] || fail "No recall arg"
      [[ -e "$REC"  ]] || fail "Can't find recalls '$REC'"

      for S in "$PREC"/*
      do
        SIZE=$(basename "$S")
         VAL=$(mean   < "$S")

        echo -e "$SIZE\t$VAL" >> prec.tsv
      done

      for S in "$REC"/*
      do
        SIZE=$(basename "$S")
         VAL=$(mean < "$S")
        echo -e "$SIZE\t$VAL" >> rec.tsv
      done

      gnuplot < "$script"
    '';
  };

  graphDims = {
    timeWidthFraction     = "1.0";
    timeHeightFraction    = "0.6";
    precRecWidthFraction  = "1.0";
    precRecHeightFraction = "0.8";
  };

  graphs = runCommand "quickspecGraphs"
    {
      script = wrap {
        name   = "getQuickSpecData.py";
        paths  = [ (python.withPackages (p: [
                     p.matplotlib p.numpy p.seaborn
                   ])) tex tetex-hack ];
        vars   = graphDims // {
          textWidth = runCommand "textWidth"
            { output = render { final = false; }; }
            ''
              set -e
              set -o pipefail
              grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' < "$output" |
                sed -e 's/WIDTH//g'                          |
                tr -d 'pt ' > "$out"
          '';
          zipped = data;
        };
        file = ./getQuickSpecData.py;
      };
    }
    ''
      set -e
      mkdir "$out"
      cd "$out"
      "$script" 1>&2
    '';
}
