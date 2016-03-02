#!/usr/bin/env bash

ERR=0 # Indicates failure, will be our exit code

# "Top-level" tests, invoked directly

function checkLatex {
    FAIL=0 # A checkLatex-specific version of ERR
    for FUNC in checkLatexUndatedTodos checkLatexDatedTodos checkLatexRefs \
                checkLatexCites checkLatexMacros checkLatexLabels          \
                checkLatexFigs checkLatexCitep
    do
        mapFiles "$FUNC" || FAIL=1
    done
    return "$FAIL"
}

function checkRender {
    render > /dev/null || {
        ERR=1
        echo "Couldn't render PDF" >> /dev/stderr
        return 1
    }
    [[ -e report.pdf ]] || {
        ERR=1
        echo "report.pdf wasn't created" >> /dev/stderr
        return 1
    }
}

function checkBibtex {
    if [[ -z "$(render | getBibStart)" ]]
    then
        ERR=1
        echo "Bibtex didn't run?" >> /dev/stderr
        return 1
    fi
}

function checkWarnings {
    BIBSTART=$(render | getBibStart)

    [[ -z "$BIBSTART" ]] && return 1

    WARNINGS=$(render | tail "-n$BIBSTART" | grep -ai "warning")

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
}

function checkPageCount {
    echo "Checking page count, without appendices" >> /dev/stderr

    disableAppendices

    RENDER="" # Invalidate cached version
    render > /dev/null || {
        ERR=1
        echo "Couldn't render without appendices" >> /dev/stderr
        restoreAppendices
        return 1
    }

    PAGES=$(pdfinfo report.pdf | grep Pages | grep -o "[0-9]*$")
    ALLOWED=15
    if [[ "$PAGES" -gt "$ALLOWED" ]]
    then
        echo "report.pdf should have $ALLOWED pages, instead has $PAGES (without appendices)" >> /dev/stderr
        ERR=1
    else
        echo "Page target is $ALLOWED, you have $PAGES (without appendices)!"
    fi

    # Put everything back
    restoreAppendices
    RENDER="" # Invalidate cached version
    render > /dev/null
}

# Per-file checks invoked by checkLatex

function checkLatexUndatedTodos {
    if grep "TODO[^{]" "$1" > /dev/null
    then
        NUM=$(grep -c TODO < "$1")
        echo "Found $NUM undated TODOs in $1" >> /dev/stderr
        ERR=1
    fi
}

function checkLatexDatedTodos {
    NOW=$(date +%s)
    while read -r TODO
    do
        D=$(echo "$TODO" | sed -e 's/.*{\(.*\)\}/\1/g')
        S=$(date --date="$D" +%s)
        [[ "$S" -gt "$NOW" ]] || {
            ERR=1
            echo "Found TODO dated '$D' in '$1'" >> /dev/stderr
        }
    done < <(grep -o "TODO{[^}]*}" < "$1")
}

function checkLatexRefs {
    # No forward-references
    [[ "x$1" = "xintro.tex" ]] || {
        while read -r REF
        do
            echo "File '$1' contains reference '$REF'" >> /dev/stderr
        done < <(grep -o '\ref{sec:[^}]*}' < "$1")
    }
}

function checkLatexCites {
    if grep CITE < "$1" > /dev/null
    then
        NUM=$(grep -c CITE < "$1")
        echo "Found $NUM missing citations in $1" >> /dev/stderr
        ERR=1
    fi
}

function checkLatexMacros {
    for MACRO in qcheck qspec hspec
    do
        while read -r USAGE
        do
            SLASH=$(echo "$USAGE" | cut -c 1)
            BRACE=$(echo "$USAGE" | rev | cut -c 1)
            [[ "x$SLASH" = 'x\' ]] || continue
            [[ "x$BRACE" = 'x{' ]] || {
                echo "Put {} after \\$MACRO in $1" >> /dev/stderr
                ERR=1
            }
        done < <(grep -v "newcommand" < "$1" |
                 grep -o ".${MACRO}.")
    done
}

function checkLatexLabels {
    # No uncategorised references
    while read -r LABEL
    do
        echo "Uncategorised label '$LABEL' in '$1'" >> /dev/stderr
        ERR=1
    done < <(grep -o '\label{[^:}]*}' < "$1")
}

function checkLatexFigs {
    # "Figure 123" should be capitalised
    while read -r FIG
    do
        echo "Uncapitalised figure '$FIG' in '$1'" >> /dev/stderr
        ERR=1
    done < <(grep -o 'figure .ref[^}]*' < "$1")
}

function checkLatexCitep {
    if grep "citep" < "$1" > /dev/null
    then
        echo "Found citep in '$1', should use cite" >> /dev/stderr
        ERR=1
    fi
}

# Helpers

function mapFiles {
    for FILE in *.tex
    do
        "$1" "$FILE"
    done
}

RENDER="" # Cache for render output. Reset to force rerendering.
RENDERFAIL=0 # Lets us fail early if rendering is broken. Don't reset this.
function render {
    # Fail fast if rendering is broken
    [[ "$RENDERFAIL" -gt 0 ]] && return 1

    # Return cached output, if we have any
    if [[ -n "$RENDER" ]]
    then
        echo "$RENDER"
        return 0
    fi

    # Perform rendering
    touch *.tex
    echo "Rendering report.tex" >> /dev/stderr
    touch *.tex
    RENDER=$(make 2>&1) || {
        echo "Couldn't render report.tex" >> /dev/stderr
        ERR=1
        RENDERFAIL=1
        echo "$RENDER" >> /dev/stderr
        return 1
    }
    echo "$RENDER"
}

function getBibStart {
     grep -an "RUNNING bibtex" | head -n1 | cut -d ':' -f 1
}

# Toggle appendices on and off, using \iffalse and \iftrue, for page counting

WITHAPPENDICES=""
WITHOUTAPPENDICES=""
function rememberAppendices {
    # Restore \iftrue/\iffalse toggle for appendices
    [[ -n "$WITHAPPENDICES" ]] || {
        CHAR=$(grep "WITH APPENDICES" < appendices.tex | grep -o "^.")
        if [[ "x$CHAR" = "x%" ]]
        then
            WITHAPPENDICES=0
        else
            WITHAPPENDICES=1
        fi
    }
    [[ -n "$WITHOUTAPPENDICES" ]] || {
        CHAR=$(grep "WITHOUT APPENDICES" < appendices.tex | grep -o "^.")
        if [[ "x$CHAR" = "x%" ]]
        then
            WITHOUTAPPENDICES=0
        else
            WITHOUTAPPENDICES=1
        fi
    }
}

function fiddleAppendices {
    sed -i -e "$1" appendices.tex
}

function enableWithAppendices {
    fiddleAppendices 's/^%\(.*WITH APPENDICES\)/\1/g'
}

function enableWithoutAppendices {
    fiddleAppendices 's/^%\(.*WITHOUT APPENDICES\)/\1/g'
}

function disableWithAppendices {
    fiddleAppendices 's/^%*\(.*WITH APPENDICES\)/%\1/g'
}

function disableWithoutAppendices {
    fiddleAppendices 's/^%*\(.*WITHOUT APPENDICES\)/%\1/g'
}

function disableAppendices {
    rememberAppendices
    enableWithoutAppendices
    disableWithAppendices
}

function restoreAppendices {
    rememberAppendices

    if [[ "$WITHAPPENDICES" -eq 0 ]]
    then
        disableWithAppendices
    else
        enableWithAppendices
    fi

    if [[ "$WITHOUTAPPENDICES" -eq 0 ]]
    then
        disableWithoutAppendices
    else
        enableWithoutAppendices
    fi
}

# Test invocation

checkLatex
checkRender
checkBibtex
checkWarnings
checkPageCount

# Report result

exit "$ERR"
