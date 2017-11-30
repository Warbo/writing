# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ nixpkgs ? import <nixpkgs> {}, bibtex ? ../../Bibtex.bib }:

with builtins;
with nixpkgs.repo1609."00ef7f9";
rec {
  graphs = callPackage ./graphs.nix { inherit teBenchmark tex textWidth; };

  # Journal of Automated Reasoning LaTeX files, from
  # http://www.springer.com/cda/content/document/cda_downloaddocument/?SGWID=0-0-45-468198-0
  latex = ./LaTeX.zip;

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  tex = (texlive.combine {
    inherit (texlive)
    scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
    frankenstein csquotes multirow type1cm;
  });

  # Render a "dummy" version of the paper which has all of the same styling, but
  # just spits out the text width to stdout. We can use this to generate figures
  # of the correct size, without having to scale things up or down.
  textWidth = runCommand "textWidth"
    {
      output = render {
        graphs = null;
        script = ''
          echo 'Getting text width' 1>&2
          touch ./graphDims.tex
          chmod +w ./article.tex
          PREAMBLE=$(grep -B 1000 '\\begin{document}' < ./article.tex)

          echo "$PREAMBLE"      >  ./article.tex
          echo "$WIDTH"         >> ./article.tex
          echo '\end{document}' >> ./article.tex
          cat ./article.tex 1>&2

          echo 'Rendering for width' 1>&2
          render | tee "$out"
        '';
      };
    }
    ''
      set -e
      set -o pipefail
      grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' < "$output" |
      sed -e 's/WIDTH//g'                          |
      tr -d 'pt ' > "$out"
    '';

  paper = render {
    inherit (graphs) graphs;
    script = ''
      ln -s "$bibtex"    ./Bibtex.bib
      [[ -z "$graphs" ]] || cp -s "$graphs"/*  ./.

      render
      bibtex article
      render
      render
      mv article.pdf "$out"
    '';
  };

  render = { graphs, script }:
    runCommand "benchmark-article.pdf"
      {
        inherit bibtex graphs latex;
        final       = if graphs == null then "false" else "true";
        WIDTH       = ''\typeout{WIDTH \the\textwidth WIDTH}'';
        src         = ./..;
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
        cp -r "$src"/* ./
        unzip "$latex"
        ${script}
      '';
}
