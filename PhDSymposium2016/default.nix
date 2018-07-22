with import <nixpkgs> {};

runCommand "phd-symposium-2015"
  {
    buildInputs = [ (import ../resources).warbo-packages."c2ea27d".pandocPkgs ];
    script      = writeScript "phdsymp16-builder" ''
      #!/usr/bin/env bash
      set -e

      # Build slides.md with Beamer
      function slides {
        pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
               --filter panpipe --filter panhandle -o "$out/slides.html" \
               "${./slides.md}"
      }

      # Build abstract.md
      function abstract {
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
        bibtex abstract
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
      }

      pids=()
      trap 'kill "${"$"}{pids[@]}"' EXIT
      slides &
      pids+=("$!")
      #abstract &
      #pids+=("$!")

      echo "Waiting for ${"$"}{pids[*]}"
      wait
    '';
  }
  ''
    mkdir "$out"
    ${concatStringsSep "\n" (map (f: ''ln -s "${./. + f}" ./${f}'') [
        "abstract.tex" "sig-alternate.cls" "templates"
    ])}
    "$script"
  ''
