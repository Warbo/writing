#!/bin/sh

function render {
  # Render a markdown file to PDF
  pdf=$(pdfOf "$1")
  pandoc --bibliography=/home/chris/Documents/ArchivedPapers/Bibtex.bib \
         --filter panpipe --filter panhandle -o "$pdf" "$1"
}

function needsUpdate {
  # Return 0 if the given Markdown file needs a new PDF generating
  md="$1"
  pdf=$(pdfOf "$md")
  if [ ! -e "$pdf" ]
  then
    return 0
  fi

  mtime=$(mtime "$md")
  ptime=$(mtime "$pdf")
  if [ "$ptime" -lt "$mtime" ]
  then
    return 0
  else
    return 1
  fi
}

function mtime {
  stat -L --printf="%Y" "$1"
}

function pdfOf {
  # Get the PDF filename to use when rendering the given Markdown file
  dir=$(dirname "$1")
  base=$(basename "$1" .md)
  echo "${dir}/${base}.pdf"
}

function renderAll {
  # Render all markdown files which need updating
  for md in $(find . -name "*.md" | grep -v "\.#")
  do
    if needsUpdate "$md"
    then
      render "$md"
    fi
  done
}

function watch {
  # Render markdown files when this directory is written to
  while true
  do
      inotifywait -q -r -e close_write . && renderAll
  done
}

# Start watching
watch
