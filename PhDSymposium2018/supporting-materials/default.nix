# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ src, bibtex, pkgs, tex }:

with builtins;
with pkgs;
rec {
  graphs = callPackage ./graphs.nix { inherit teBenchmark tex textWidth; };

  comparison = callPackage ./comparison.nix {
    inherit (graphs) isacosyData quickspecData;
  };

  # Render a "dummy" version of the paper which has all of the same styling, but
  # just spits out the text width to stdout. We can use this to generate figures
  # of the correct size, without having to scale things up or down.
  textWidth = runCommand "text-width"
    {
      inherit bibtex src;
      buildInputs = [ jq tex unzip ];
    }
    ''
      set -e
      set -o pipefail

      mkdir src
      cp -s "$src"/*  ./src/
      ln -s "$bibtex" ./Bibtex.tex
      cd ./src

      PREAMBLE=$(grep -B 1000 '\\begin{document}' < abstract.tex)
      rm abstract.tex

      echo "$PREAMBLE"                            >  ./abstract.tex
      echo '\typeout{WIDTH \the\textwidth WIDTH}' >> ./abstract.tex
      echo '\end{document}'                       >> ./abstract.tex

      pdflatex -interaction=nonstopmode -halt-on-error \
               --shell-escape abstract     |
        grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' |
        sed -e 's/WIDTH//g'                |
        tr -d 'pt ' > "$out"
    '';
}
