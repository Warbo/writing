{ fail, fetchgit, gnuplot, jq, miller, mkBin, python, runCommand, wrap,
  writeScript }:

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

  timePlot = wrap {
    name   = "timePlot";
    paths  = [ fail gnuplot miller ];
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$1" ]] || fail "No arg given"
      [[ -e "$1" ]] || fail "No such file '$1'"

      #echo "set terminal epslatex size 8.89cm,6.65cm color colortext
      #      set output 'times.tex'
      echo "set terminal pngcairo size 350,262 enhanced font 'Verdana,10'
            plot '$1'" | gnuplot
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
        plot prec title "Precision", \
             rec  title "Recall"
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$1" ]] || fail "No precision arg"
      [[ -e "$1" ]] || fail "No such file '$1'"
      [[ -n "$2" ]] || fail "No recall arg"
      [[ -e "$2" ]] || fail "No such file '$2'"

      PREC="$1" REC="$2" gnuplot < "$script"
    '';
  };

  quickspecGraphs = runCommand "quickspecGraphs"
    {
      inherit precRecPlot quickspecData timePlot;
      buildInputs = [ mean median miller ];
    }
    ''
      for FIELD in time prec rec
      do
        for S in "$quickspecData/$FIELD"/*
        do
          SIZE=$(basename "$S")
          if [[ "x$FIELD" = "xtime" ]]
          then
            VAL=$(median < "$S")
          else
            VAL=$(mean   < "$S")
          fi
          echo -e "$SIZE\t$VAL" >> "$FIELD.dat"
        done
      done

      mkdir "$out"
      "$timePlot"    time.dat         > "$out/time.png"
      "$precRecPlot" prec.dat rec.dat > "$out/precRec.png"
    '';

  quickspecData = runCommand "quickspecData"
    {
      script = wrap {
        name   = "getQuickSpecData.py";
        paths  = [ python ];
        vars   = { zipped = data; };
        script = ''
          #!/usr/bin/env python
          import os
          import sys
          msg = sys.stderr.write
          get = lambda x, *path: x if path == () else get(x[path[0]], *path[1:])
          num = lambda x: type(x) in [type(42), type(42.0)]

          msg('Gathering input\n')
          import gzip
          import json
          with gzip.open(os.getenv('zipped'), 'r') as zipped:
            data = get(json.load(zipped),
                       'results', 'quickspectip.track_data', 'result', 0)

          msg('Setting up output\n')
          out = os.getenv('out')
          prec, rec, time = [out + '/' + x for x in ['prec', 'rec', 'time']]
          map(os.mkdir, [out, prec, rec, time])
          del out

          for size in data:
            msg('Extracting data for size {0}\n'.format(size))
            sdata   = data[size]['reps']
            samples = []
            with open(prec + '/' + size, 'w') as precs, \
                 open(rec  + '/' + size, 'w') as recs,  \
                 open(time + '/' + size, 'w') as times:
              for rep in sorted(sdata.keys()):
                rdata = sdata[rep]

                sample = sorted(rdata['sample'])
                if sample in samples:
                  msg('Size {0} rep {1} is a dupe, skipping\n'.format(
                    size, rep))
                else:
                  samples += [sample]

                  # Get the time if available, otherwise treat as a timeout
                  # We use min since killing might take some time
                  t = min(rdata['time'], rdata['timeout'])
                  assert num(t), 'Non-numeric time %r' % type(t)
                  times.write(str(t) + '\n')

                  # Assume precision is 0 if not found
                  p = rdata['precision'] if 'precision' in rdata else 0
                  p = p or 0
                  assert num(p), 'Non-numeric prec %r' % type(p)
                  precs.write(str(p) + '\n')

                  # Assume recall is 0 if not found
                  r = rdata['recall'] if 'recall' in rdata else 0
                  r = r or 0
                  assert num(r), 'Non-numeric rec %r' % type(r)
                  recs.write(str(r) + '\n')
        '';
      };
    }
    ''
      set -e
      "$script" 1>&2
    '';
}
