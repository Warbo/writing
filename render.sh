#!/bin/sh

# Render all markdown files to PDF

for md in $(find . -name "*.md")
do
    dir=$(dirname "$md")
    base=$(basename "$md" .md)
    pdf="${dir}/${base}.pdf"
    pandoc --bibliography=/home/chris/Documents/ArchivedPapers/Bibtex.bib \
           --filter panpipe --filter panhandle -o "$pdf" "$md"
done
