{ basicTex, bucketingSrc, lib, lzip, python3, rPackages, run, runCommand,
  runner, rWrapper, textWidth, wrap }:

with lib;
with rec {
  extracter = wrap {
    name  = "pairwise-clustering-hash";
    file  = ./pairwiseData.py;
    paths = [
      basicTex  # FIXME: Remove this, although it'll cause a rebuild (overnight?)
      (python3.withPackages (p: [ p.ijson p.scipy ]))
    ];
    vars = { inherit wilcoxon; };
  };

  # Annoyingly, SciPy's implementation of Wilcoxon uses a normal approximation,
  # which is invalid for small sample sizes (when ties are discarded).
  wilcoxon = wrap {
    name  = "wilcoxon-signed-rank";
    paths = [ (rWrapper.override { packages = [ rPackages.coin ]; }) ];
    vars  = {
      code = wrap {
        name   = "wilcoxon.R";
        script = ''
          library(coin)
          lines <- readLines(con="filenames")
          message(sprintf("Need to process %d files\n", length(lines)))
          for (i in 1:length(lines)) {
            df <- read.csv(file=lines[i], header=FALSE, sep=",")
            x  <- df[,1]
            y  <- df[,2]
            cat(sprintf("%f\n",
              pvalue(wilcoxsign_test(x ~ y, paired=TRUE,
                                     distribution='exact', correct=FALSE,
                                     alternative="greater",
                                     zero.method=c('Pratt')))))
          }
        '';
      };
    };
    script = ''
      #!/usr/bin/env bash
      Rscript --no-save --no-restore --verbose "$code"
    '';
  };

  data = concatStringsSep "/" [
    "${bucketingSrc}"
    "experiment-results"
    "89132d7"
    "withBucketsGroundTruths.json.lz"
  ];

  processed = runCommand "pairwise-clustering-hash"
    {
      script = wrap {
        name   = "pairwise-analyser";
        paths  = [ lzip ];
        script = ''
          lzip -d < "${data}" | "${extracter}" > out
          rm -f filenames
          find . -name '*.csv' | while read -r F; do rm -f "$F"; done
        '';
      };
    }
    runner;

  graph = run {
    name  = "pairwise-graph";
    file  = ./grapher.py;
    paths = [ basicTex (python3.withPackages (p: [ p.matplotlib ])) ];
    vars  = { inherit processed textWidth; };
  };
};
{ inherit graph processed; }
