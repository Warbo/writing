#! /usr/bin/env nix-shell
#! nix-shell -p bash -p pandoc -i bash

shopt -s globstar
for REL in stp/**/*.md
do
    ABS=$(readlink -f "$REL")
    DIR=$(dirname "$ABS")
    NAME=$(basename "$ABS" .md)
    cd "$DIR"
    pandoc -i "$NAME.md" -o "$NAME.html"
done
