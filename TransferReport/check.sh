#!/usr/bin/env bash

cd /home/chris/Writing/TransferReport
ERR=0

TODOS=""
REFS=""
CITES=""
MACROS=""
LABELS=""
FIGS=""
for FILE in *.tex
do
    if grep "TODO[^{]" < "$FILE" > /dev/null
    then
        NUM=$(grep -c TODO < "$FILE")
        TODOS=$(echo "$TODOS"; echo "Found $NUM undated TODOs in $FILE")
        ERR=1
    fi

    NOW=$(date +%s)
    while read -r TODO
    do
        D=$(echo "$TODO" | sed -e 's/.*{\(.*\)\}/\1/g')
        S=$(date --date="$D" +%s)
        [[ "$S" -gt "$NOW" ]] || {
            ERR=1
            TODOS=$(echo "$TODOS"; echo "Found TODO dated '$D' in '$FILE'")
        }
    done < <(grep -o "TODO{[^}]*}" < "$FILE")

    if grep CITE < "$FILE" > /dev/null
    then
        NUM=$(grep -c CITE < "$FILE")
        CITES=$(echo "$CITES"; echo "Found $NUM missing citations in $FILE")
        ERR=1
    fi

    for MACRO in qcheck qspec hspec
    do
        while read -r USAGE
        do
            SLASH=$(echo "$USAGE" | cut -c 1)
            BRACE=$(echo "$USAGE" | rev | cut -c 1)
            [[ "x$SLASH" = 'x\' ]] || continue
            [[ "x$BRACE" = 'x{' ]] || {
                MACROS=$(echo "$MACROS"; echo "Put {} after \\$MACRO in $FILE")
                ERR=1
            }
        done < <(grep -v "newcommand" < "$FILE" |
                 grep -o ".${MACRO}.")
    done

    # No uncategorised references
    while read -r LABEL
    do
        LABELS=$(echo "$LABELS"; echo "Uncategorised label '$LABEL' in '$FILE'")
        ERR=1
    done < <(grep -o '\label{[^:}]*}' < "$FILE")

    # No forward-references
    [[ "x$FILE" = "xintro.tex" ]] || {
        while read -r REF
        do
            REFS=$(echo "$REFS"; echo "File '$FILE' contains reference '$REF'")
        done < <(grep -o '\ref{sec:[^}]*}' < "$FILE")
    }

    # "Figure 123" should be capitalised
    while read -r FIG
    do
        FIGS=$(echo "$FIGS"; echo "Uncapitalised figure '$FIG' in '$FILE'")
        ERR=1
    done < <(grep -o 'figure .ref[^}]*' < "$FILE")
done

[[ -z "$TODOS"  ]] || echo "$TODOS"  >> /dev/stderr
[[ -z "$REFS"   ]] || echo "$REFS"   >> /dev/stderr
[[ -z "$CITES"  ]] || echo "$CITES"  >> /dev/stderr
[[ -z "$MACROS" ]] || echo "$MACROS" >> /dev/stderr
[[ -z "$LABELS" ]] || echo "$LABELS" >> /dev/stderr
[[ -z "$FIGS"   ]] || echo "$FIGS"   >> /dev/stderr

echo "Rendering report.tex" >> /dev/stderr
touch *.tex
RENDER=$(make 2>&1) || {
    echo "Couldn't render report.tex"
    ERR=1
}

echo "Checking output of renderer" >> /dev/stderr
BIBSTART=$(echo "$RENDER" | grep -an "RUNNING bibtex" | head -n1 | cut -d ':' -f 1)
if [[ -z "$BIBSTART" ]]
then
    echo "$RENDER"
    ERR=1
    echo "Bibtex didn't run?" >> /dev/stderr
else
    WARNINGS=$(echo "$RENDER" | tail "-n$BIBSTART" | grep -ai "warning")

    # Citations take two passes, so double-check
    CITES=$(echo "$WARNINGS" | grep 'Citation `'  | sed -e 's/.*`\(.*\)'"'.*/\1/g")
    while read -r CITE
    do
        grep "^@[^{]*{$CITE,$" < ~/Writing/Bibtex.bib > /dev/null ||
        {
            ERR=1
            echo "Citation '$CITE' missing" >> /dev/stderr
        }
    done < <(echo "$CITES")

    # Check for non-citation warnings
    NONCIT=$(echo "$WARNINGS" | grep -v 'Citation `'                      |
                                grep -v "There were undefined citations." |
                                grep -v "Citation(s) may have changed."   |
                                grep -v "Rerun to get cross-references right.")
    [[ -z "$NONCIT" ]] || {
        echo "$NONCIT" >> /dev/stderr
        echo "There were warnings from the renderer" >> /dev/stderr
    }
fi

if [[ -e report.pdf ]]
then
    PAGES=$(pdfinfo report.pdf | grep Pages | grep -o "[0-9]*$")
    TOTAL=60
    REMAINING=$(( TOTAL - PAGES ))
    NOW=$(date +%s)
    DEADLINE=$(date -d "2015-12-17" +%s)
    DAYS=$(( (DEADLINE - NOW) / (60 * 60 * 24) ))
    SHOULD=$(( TOTAL - DAYS ))
    if [[ "$REMAINING" -gt "$DAYS" ]]
    then
        echo "report.pdf should have $SHOULD pages by now, only has $PAGES" >> /dev/stderr
    else
        echo "Page target is $SHOULD, you have $PAGES!"
    fi
fi

exit "$ERR"
