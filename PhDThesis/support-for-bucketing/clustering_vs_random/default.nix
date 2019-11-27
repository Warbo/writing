{ basicTex, bucketingSrc, lib, lzip, python3, rPackages, runCommand, runner,
  rWrapper, textWidth, wrap }:

with lib;
with rec {
  grapher = wrap {
    name  = "pairwise-clustering-hash";
    file  = ./pairwiseGraph.py;
    paths = [
      basicTex
      (python3.withPackages (p: [ p.ijson p.matplotlib p.scipy ]))
    ];
    vars = { inherit textWidth wilcoxon; };
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
          df <- read.csv(file="stdin", header=FALSE, sep=",")
          x  <- df[,1]
          y  <- df[,2]
          wilcoxsign_test(x ~ y, data=df, paired=TRUE,
                          distribution='exact', correct=FALSE,
                          alternative="greater",
                          zero.method = c('Pratt'))
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

  pairwise = runCommand "pairwise-clustering-hash"
    {
      script = wrap {
        name   = "pairwise-analyser";
        paths  = [ lzip ];
        script = ''
          lzip -d < "${data}" | "${grapher}" | tee out
        '';
      };
    }
    runner;
};
{ inherit pairwise wilcox; }
