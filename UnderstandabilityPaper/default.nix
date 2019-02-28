with { inherit (import ../resources) bibtex nixpkgs-joined; };
with nixpkgs-joined;
runCommand "machinelearning.pdf"
  {
    inherit bibtex;
    buildInputs = [ (texlive.combine { inherit (texlive) scheme-small; }) ];
    f           = ./machinelearning.tex;
  }
  ''
    ln -s "$f"      machinelearning.tex
    ln -s "$bibtex" Bibtex.bib

    function go {
      echo "Running pdflatex" 1>&2
      pdflatex machinelearning
    }

    go
    go
    #echo "Running bibtex" 1>&2
    #bibtex machinelearning
    go
    mv machinelearning.pdf "$out"
  ''
