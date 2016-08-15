{ fetchurl, latestGit, stdenv, texlive }:

let haskell-te = null;#latestGit { url = http://chriswarbo.net/git/haskell-te.git; };
 in stdenv.mkDerivation {
      name = "ml4hs-tech-report";
      src  = ./.;

      styles = map fetchurl [
        { url    = "http://cristal.inria.fr/~remy/latex/mathpartir.sty";
          sha256 = "0r6l1x7339b6ni8mq0pyqmj9ivwzxqhaas5rjw4xhr558jn648n1"; }
        { url    = "http://www.ccs.neu.edu/course/csg264/latex/mmm.sty";
          sha256 = "0qwhx1zf55dffiqg4np9xb34gzw571n8xkcvf0915ffp8qq20ki4"; }
        { url = "http://anorien.csc.warwick.ac.uk/mirrors/CTAN/graphics/psfig/psfig.sty";
          sha256 = "043pw8p7wbwjaiaf6gsnx2r36q7q2b6ardl3srx8nm8wdkqk5ap7"; }
      ];

      cmd = "pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report";

      buildInputs = [ (texlive.combine {
                        inherit (texlive) collection-latexrecommended
                                          algorithmicx algorithms paralist
                                          listings csquotes etoolbox epsf
                                          tikz-qtree titlesec;
                      }) ];

      buildCommand = ''
        source $stdenv/setup

        cp -r "$src" ./src
        chmod +w -R ./src
        cd ./src

        for S in $styles
        do
          cp "$S" .
        done

        cp "${../Bibtex.bib}" ./Bibtex.bib

        $cmd

        echo "RUNNING bibtex"
        bibtex report

        $cmd
        $cmd

        cp report.pdf "$out"
      '';
    }
