#! /usr/bin/env nix-shell
#! nix-shell -p bash -p pandoc -i bash

echo "Checking contents of stp/"
while IFS= read -r -d $'\0' FILE
do
    echo "Do not know how to process $FILE, aborting"
    exit 1
done < <( find stp/ -type f -not -name '*.md' -print0 )
echo "OK"

echo "Removing old version"
rm -r rendered/

echo "Rendering all Markdown files to HTML"
shopt -s globstar
for REL in stp/**/*.md
do
    DIR=$(dirname "$REL")
    NAME=$(basename "$REL" .md)
    mkdir -p "rendered/$DIR"
    pandoc -i "$DIR/$NAME.md" -o "rendered/$DIR/$NAME.html"
done
