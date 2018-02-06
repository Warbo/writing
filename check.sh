#!/usr/bin/env bash
set -e
set -o pipefail

# Various simple, fast checks of documents and bibliographies. This can be
# useful to run automatically, e.g. as a git hook on pre-commit or post-receive.

function msg {
    echo -e "$*" 1>&2
}

function haveCommand {
    command -v "$1" 1> /dev/null 2> /dev/null
}

msg "Sanity checking..."
ERR=0

[[ -e Bibtex.bib ]] || {
    msg "Couldn't find Bibtex.bib; ensure script is run from writing dir/repo"
    exit 1
}

DIR=$(mktemp -d -t 'writing-check-XXXXX')

function cleanUp {
    rm -rf "$DIR"
}

trap cleanUp EXIT

if haveCommand bibtool
then
    msg "Checking Bibtex.bib with bibtool"
    bibtool -d < Bibtex.bib > /dev/null 2> "$DIR/bibtool.stderr"
else
    msg "Couldn't find bibtool command"
    echo "" > "$DIR/bibtool.stderr"
    ERR=1
fi

if grep -v 'non-space characters ignored' < "$DIR/bibtool.stderr" |
   grep '^.' 1>&2
then
    msg "bibtool spotted problems (other than 'ignored chars', AKA comments)"
    ERR=1
fi

if haveCommand bibclean
then
    msg "Checking Bibtex.bib with bibclean"
    bibclean < Bibtex.bib > /dev/null 2> "$DIR/bibclean.stderr" || true
else
    msg "Couldn't find bibclean command"
    echo "" > "$DIR/bibclean.stderr"
    ERR=1
fi

# NOTE: bibclean spots a lot of problems, so we filter out common annoyances.
# It's a good idea, if you currently have the time, to remove some of these
# filters and fix the offending entries.
for PAT in 'Invalid checksum for ISBN' \
           'prefix in DOI value'       \
           'volume ='                  \
           'Suspicious year'           \
           'year ='                    \
           'pages ='                   \
           '?? "stdin", line 1: Expected comma after last field'
do
    grep -v "$PAT" < "$DIR/bibclean.stderr" > "$DIR/bibclean.stderr2" || true
    mv "$DIR/bibclean.stderr2" "$DIR/bibclean.stderr"
done

if grep '^.' < "$DIR/bibclean.stderr" 1>&2
then
    msg "bibclean spotted problems with Bibtex.bib"
    ERR=1
fi

exit "$ERR"
