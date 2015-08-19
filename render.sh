#! /usr/bin/env nix-shell
#! nix-shell -p bash -p pandoc -i bash

FORMATS="png jpg ico"

function check {
    # Directories are OK
    [[ -d "$1" ]] && return 0

    # Check filename extension against ones we know how to process
    EXT=$(echo "$1" | rev | cut -d '.' -f 1 | rev)
    for KNOWN in md $FORMATS
    do
        [[ "x$EXT" = "x$KNOWN" ]] && return 0
    done
    echo "Don't know how to handle $1" >> /dev/stderr
    exit 1
}

function copy {
    DIR=$(dirname "$1")
    mkdir -p "rendered/$DIR"
    cp -v "$1" "rendered/$DIR/"
}

function copyAll {
    for FILE in stp/**/*."$1"
    do
        copy "$FILE"
    done
}

echo "Checking contents of stp/"
shopt -s globstar
for file in stp/**/*
do
    check "$file"
done

echo "Removing old version"
rm -r rendered/

echo "Rendering all Markdown files to HTML"
for REL in stp/**/*.md
do
    DIR=$(dirname "$REL")
    NAME=$(basename "$REL" .md)
    mkdir -p "rendered/$DIR"
    pandoc -s -i "$REL" -o "rendered/$DIR/$NAME.html"
done

echo "Putting images in place"
for FORMAT in $FORMATS
do
    copyAll "$FORMAT"
done
