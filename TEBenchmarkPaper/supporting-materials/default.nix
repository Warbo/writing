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

  # The final paper, with all graphs, etc.
  paper = render {
    inherit article;
    inherit (comparison) qualityComparison timeComparison;
    inherit (graphs    ) graphs;
    name   = "benchmark-article.pdf";
    script = ''
      ln -s "$bibtex" ./Bibtex.bib
      [[ -z "$graphs"            ]] || cp -rs "$graphs"/*            ./.
      [[ -z "$qualityComparison" ]] || cp -rs "$qualityComparison"/* ./.
      [[ -z "$timeComparison"    ]] || cp -rs "$timeComparison"/*    ./.

      render
      bibtex article
      render
      render
      mv article.pdf "$out"
    '';
  };

  render = { article, graphs, name, script, qualityComparison, timeComparison }:
    runCommand name
      {
        inherit article bibtex graphs latex qualityComparison timeComparison;
        buildInputs = [
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
    csvsimple scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
    algorithms enumitem frankenstein csquotes multirow type1cm;
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
