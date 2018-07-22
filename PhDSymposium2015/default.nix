with import <nixpkgs> {};

runCommand "phd-symposium-2015"
  {
    buildInputs = [ (import ../resources).warbo-packages."c2ea27d".pandocPkgs ];
    buildScript = writeScript "PhDSymposium2015-builder" ''
      #!/usr/bin/env bash
      set -e

      # Build slides.md with Beamer
      function slides {
        pandoc -w dzslides --standalone --self-contained \
               --filter pandoc-citeproc -o "$out/slides.html" "${./slides.md}"
      }

      # Build abstract.md
      function abstract {
        pandoc --template=./templates/default.latex -o "$out/abstract.pdf" \
               -N "${./abstract.md}"
      }

      pids=()
      trap 'kill "${"$"}{pids[@]}"' EXIT
      slides &
      pids+=("$!")
      abstract &
      pids+=("$!")

      echo "Waiting for "${"$"}{pids[*]}"
      wait
    '';
  }
  ''
    mkdir "$out"
    ln -s "${./acm_proc_article-sp.cls}" ./acm_proc_article-sp.cls
    ln -s "${./acm-sig-proceedings.csl}" ./acm-sig-proceedings.csl
    ln -s "${./sig-alternate.cls}"       ./sig-alternate.cls
    ln -s "${./templates}"               ./templates
    "$buildScript"
  ''
