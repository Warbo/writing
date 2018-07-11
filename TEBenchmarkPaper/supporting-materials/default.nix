# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ nixpkgs ? import <nixpkgs> {}, bibtex ? ../../Bibtex.bib }:

with builtins;
with nixpkgs.repo1609."00ef7f9";
rec {
  article = ../article.tex;

  graphs = callPackage ./graphs.nix { inherit tex textWidth; };

  comparison = callPackage ./comparison.nix {
    inherit (graphs) isacosyData quickspecData;
  };

  # Journal of Automated Reasoning LaTeX files, from
  # http://www.springer.com/cda/content/document/cda_downloaddocument/?SGWID=0-0-45-468198-0
  latex = ./LaTeX.zip;

  styFinder = wrap {
    name   = "styfinder.py";
    paths  = [ python ];
    script = ''
      #!/usr/bin/env python
      import re
      import sys
      replace      = lambda old, new: lambda s: s.replace(old, new)
      join_lines   = replace("/\ntex", "/tex")
      strip_prefix = replace("(/nix/store", "/nix/store")

      for m in re.finditer('/nix/store/[^ \n]*\.sty',
                           strip_prefix(join_lines(sys.stdin.read()))):
        print(m.group())
    '';
  };

  # The final paper, with all graphs, etc. built from the directory we're going
  # to send to the publisher.
  paper = runCommand "benchmark-paper"
    {
      inherit latex;
      buildInputs = [
        ghostscript
        (mkBin {
          name   = "repstopdf";
          paths  = [ bash ];
          script = ''
            #!/usr/bin/env bash
            command -v epstopdf || {
              echo "No epstopdf command found!" 1>&2
              exit 1
            }
            epstopdf --restricted "$@"
          '';
        })
        (texlive.combine { inherit (texlive) epstopdf scheme-medium; })
        unzip
      ];
      src     = finalMaterials;
      article = "${finalMaterials}/article.tex";
    }
    ''
      cp -r "$src" "$out"
      cp -r "$src" ./src
      chmod +w -R  ./src "$out"
      cd src/
      unzip "$latex"
      pdflatex -interaction=nonstopmode -halt-on-error article
      bibtex article
      pdflatex -interaction=nonstopmode -halt-on-error article
      pdflatex -interaction=nonstopmode -halt-on-error article
      cp article.pdf "$out"/
    '';

  # Render the paper in a "sane" way (using a LaTeX installation with the
  # required packages, generating fresh figures from the data, using
  # semantically meaningful filenames, using a unified bibtex database, etc.).
  # We then inspect the build logs to find style files, citations, etc. and
  # construct a directory containing copies of those things.
  finalMaterials = render {
    inherit article;
    inherit (comparison) qualityComparison timeComparison;
    inherit (graphs    ) graphs;
    name   = "final-materials";
    script = ''
      ln -s "$bibtex" ./Bibtex.bib
      [[ -z "$graphs"            ]] || {
        cp "$graphs"/quickspectime.eps ./Fig3.eps
        cp "$graphs"/quickspecprec.eps ./Fig4.eps
        cp "$graphs"/isacosytime.eps   ./Fig5.eps
        cp "$graphs"/isacosyprec.eps   ./Fig6.eps
      }
      [[ -z "$qualityComparison" ]] || cp -rs "$qualityComparison"/* ./.
      [[ -z "$timeComparison"    ]] || cp -rs "$timeComparison"/*    ./.

      function go {
        render 1> >(tee -a STDOUT.txt)
        bibtex article
        render 1> >(tee -a STDOUT.txt)
        render 1> >(tee -a STDOUT.txt)
      }

      mkdir "$out"

      PRE='\begin{filecontents*}{speedups.csv}'
      POST='\end{filecontents*}'
      DATA=$(cat speedups.csv)
      SPEEDUPDATA=$(printf '%s\n%s\n%s' "$PRE" "$DATA" "$POST")

      rm speedups.csv
      replace "%INCLUDE SPEEDUP CSV HERE" "$SPEEDUPDATA" -- article.tex

      echo "Initial render to figure out bibliography and generate figures" 1>&2
      go || {
        for F in *.log
        do
          echo "CONTENTS OF $F" 1>&2
          cat "$F" 1>&2
        done
        exit 1
      }

      echo "Extracting relevant Bibtex entries" 1>&2
      bibtool -x article.aux -o NewBib.bib
      mv -v NewBib.bib "$out/Bibtex.bib"

      echo "Copying EPS figures (non-TikZ)" 1>&2
      cp -v Fig*.eps "$out"/

      echo "Looking for style files" 1>&2
      STYLES=$("${styFinder}" < STDOUT.txt | sort -u)
      echo "$STYLES" | while read -r STYLE
      do
        cp -v "$STYLE" "$out"/
      done

      echo "Copying CSV data" 1>&2
      cp -v *.csv "$out"/

      cp -v article.tex "$out"/
    '';
  };

  render = { article, graphs, name, script, qualityComparison, timeComparison }:
    runCommand name
      {
        inherit article bibtex graphs latex qualityComparison timeComparison;
        buildInputs = [
          bibtool
          ghostscript
          poppler_utils # For pdftops
          replace
          tex
          unzip
          (mkBin {
            name   = "render";
            script = ''
              #!/usr/bin/env bash
              exec pdflatex -interaction=nonstopmode \
                            -halt-on-error \
                            --shell-escape article
            '';
          })
        ];
      }
      ''
        set -e
        unzip "$latex"
        cp "$article" ./article.tex
        ${script}
      '';

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  tex = (texlive.combine {
    inherit (texlive)
      collection-binextra csvsimple scheme-small tikzinclude tikz-qtree
      algorithmicx algorithm2e algorithms enumitem epstopdf frankenstein
      csquotes multirow standalone type1cm;
  });

  # Render a "dummy" version of the paper which has all of the same styling, but
  # just spits out the text width to stdout. We can use this to generate figures
  # of the correct size, without having to scale things up or down.
  textWidth = render {
    article = writeScript "article-width.tex" (import (runCommand "widthTex.nix"
      {
        inherit article;
        buildInputs = [ jq ];
      }
      ''
        PREAMBLE=$(grep -B 1000 '\\begin{document}' < "$article")

        echo "$PREAMBLE"                            >  ./article.tex
        echo '\typeout{WIDTH \the\textwidth WIDTH}' >> ./article.tex
        echo '\end{document}'                       >> ./article.tex

        jq -Rs '.' < ./article.tex > "$out"
      ''));
    name    = "text-width";
    script  = ''
      set -o pipefail
      render | tee ./output
      grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' < ./output |
      sed -e 's/WIDTH//g'                           |
      tr -d 'pt ' > "$out"
    '';

    # Prevent infinite recursion
    graphs            = null;
    qualityComparison = null;
    timeComparison    = null;
  };
}
