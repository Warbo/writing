#!/usr/bin/env bash

# Build slides.md with Beamer
function slides {
    pandoc -w dzslides --standalone --self-contained --filter pandoc-citeproc -o slides.html slides.md
}

# Build abstract.md
function abstract {
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    bibtex abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
    pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
}

pids=()
trap 'kill "${pids[@]}"' EXIT
slides &
pids+=("$!")
abstract &
pids+=("$!")

echo "Waiting for ${pids[*]}"
wait
