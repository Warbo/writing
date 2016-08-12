#!/usr/bin/env bash

# Build slides.md with Beamer
function slides {
    pandoc -w dzslides --standalone --self-contained --filter pandoc-citeproc -o slides.html slides.md
}

# Build abstract.md
function abstract {
    pandoc --template=./templates/default.latex -N abstract.md
}

pids=()
trap 'kill "${pids[@]}"' EXIT
slides &
pids+=("$!")
abstract &
pids+=("$!")

echo "Waiting for ${pids[*]}"
wait
