{ bibtex, lib, poppler_utils, render, runCommand, utillinux, wrap }:

with builtins;
with lib;
with rec {
  getBibStart = ''
    # Drops lines from stdin until a sentinel from 'render' is reached, which
    # tells us that output from 'bibtex' follows
    function getBibStart {
      grep -an "RUNNING bibtex" | head -n1 | cut -d ':' -f 1 || {
        echo "Didn't find Bibtex sentinel" 1>&2
        exit 1
      }
    }
  '';

  fileNames = attrNames (readDir ./..);

  texs = filter (hasSuffix ".tex") fileNames;

  texFiles = map (f: ./.. + "/${f}") (filter (hasSuffix ".tex") texs);
};
{
  checkLatex = mapAttrs (n: f: genAttrs texs (t:
                                 runCommand "checkLatex-${n}-${t}"
                                   {
                                     buildInputs = [ utillinux ];
                                   }
                                   ''
                                     ERR=0
                                     ${f (./.. + "/${t}")}
                                     [[ "$ERR" -eq 0 ]] || exit 1
                                     mkdir "$out"
                                   '')) {
    checkLatexUndatedTodos = f: ''
      if grep "TO""DO[^{]" "${f}" > /dev/null
      then
        NUM=$(grep -c "TO""DO" < "${f}")
        echo "Found $NUM undated TO""DOs in ${f}"
        exit 1
      fi
    '';

    checkLatexDatedTodos = f: ''
      NOW=$(date +%s)
      while read -r TD
      do
        D=$(echo "$TD" | sed -e 's/.*{\(.*\)\}/\1/g')
        S=$(date --date="$D" +%s)
        [[ "$S" -gt "$NOW" ]] || {
          echo "Found TO""DO dated '$D' in '${f}'"
          ERR=1
        }
      done < <(grep -o "TO""DO{[^}]*}" < "${f}")
    '';

    checkLatexRefs = f: ''
      LABELS=""
      for F in ${concatStringsSep " " texFiles}
      do
        THESE=$(grep -o '\\label{[^}]*}' < "$F") || true
        LABELS=$(echo "$LABELS"; echo "$THESE")
      done

      ERR=0
      [[ "x$1" = "xintro.tex" ]] || {
        while read -r REF
        do
          if echo "$LABELS" | grep -o "label{$REF}" > /dev/null
          then
            # Report references, to allow checking for forward references
            echo "File '${f}' contains reference '$REF'" 1>&2
          else
            echo "File '${f}' contains unknown reference '$REF'" 1>&2
            ERR=1
          fi
        done < <(grep -o '\ref{sec:[^}]*}' < "${f}" |
                 grep -o '{.*}'                     |
                 grep -o "[^{}]*")
      }
    '';

    checkLatexCites = f: ''
      # Check citations exist in Bibtex.bib

      function citationExists {
        grep "^@[^{]*{$1,$" < "${bibtex}" > /dev/null
      }

      # We need to handle optional arguments like \cite[foo]{bar}
      while read -r CITE
      do
        citationExists "$CITE" || {
          echo "Citation '$CITE' in '${f}' wasn't found" 1>&2
          ERR=1
        }
      done < <(grep -o '\\cite[^{]*{[^}]*' < "${f}" |
               sed -e 's/.*{//g'                    |
               tr ',' '\n')
    '';

    checkLatexCiteTodos = f: ''
      # Write "CITE" to mean 'citation needed'
      if grep CITE < "${f}" > /dev/null
      then
        NUM=$(grep -c CITE < "${f}")
        echo "Found $NUM missing citations in ${f}" 1>&2
        exit 1
      fi
    '';

    checkLatexMacros = f: ''
      for MACRO in qcheck qspec hspec
      do
        while read -r USAGE
        do
          SLASH=$(echo "$USAGE" | cut -c 1)
          BRACE=$(echo "$USAGE" | rev | cut -c 1)

          # shellcheck disable=SC1003
          [[ "x$SLASH" = 'x\' ]] || continue

          [[ "x$BRACE" = 'x{' ]] || {
            echo "Put {} after \\$MACRO in ${f}" 1>&2
            ERR=1
          }
        done < <(grep -v "newcommand" < "${f}" |
                 grep -o ".$MACRO.")
      done
    '';

    checkLatexLabels = f: ''
      # No uncategorised references
      while read -r LABEL
      do
        echo "Uncategorised label '$LABEL' in '${f}'" 1>&2
        ERR=1
      done < <(grep -o '\label{[^:}]*}' < "${f}")
    '';

    checkLatexFigs = f: ''
      # "Figure 123" should be capitalised
      while read -r FIG
      do
        echo "Uncapitalised figure '$FIG' in '${f}'" 1>&2
        ERR=1
      done < <(grep -o 'figure .ref[^}]*' < "${f}")
    '';

    checkLatexCitep = f: ''
      if grep "citep" < "${f}" > /dev/null
      then
        echo "Found citep in '${f}', should use cite" 1>&2
        exit 1
      fi
    '';

    checkLatexDupeCites = f: ''
      while read -r CITE
      do
        COUNT=0
        for F in ${concatStringsSep " " texFiles}
        do
          THESE=$(grep -c "cite[^{]*{$CITE}" < "$F") || true
          COUNT=$(( COUNT + THESE ))
        done

        if [[ "$COUNT" -lt 1 ]]
        then
          echo "Citation '$CITE' appears '$COUNT' times, which seems wrong" 1>&2
        elif [[ "$COUNT" -gt 1 ]]
        then
          echo "Cited '$CITE' '$COUNT' times" 1>&2
        fi
      done < <(grep -o 'cite[^{]*{[^}]*' < "${f}" | sed -e 's/.*{//g')
    '';
  };

  checkBibtex = runCommand "check-bibtex" { inherit render; } ''
    ${getBibStart}

    GOT=$("$render" | getBibStart)
    if [[ -z "$GOT" ]]
    then
      echo "Bibtex didn't run?" 1>&2
      exit 1
    fi
    mkdir "$out"
  '';

  checkWarnings = runCommand "check-warnings" { inherit render; } ''
    ${getBibStart}

    "$render" > stdout
    BIBSTART=$(getBibStart < stdout)

    [[ -z "$BIBSTART" ]] && {
      echo "No Bibtex output" 1>&2
      exit 1
    }

    WARNINGS=$(tail "-n$BIBSTART" < stdout | grep -ai "warning")

    # Citations take two passes, so double-check
    CITES=$(echo "$WARNINGS" | grep 'Citation `' |
                               sed -e 's/.*`\(.*\)'"'.*/\\1/g")
    while read -r CITE
    do
      grep "^@[^{]*{$CITE,$" < ./Bibtex.bib > /dev/null || {
        ERR=1
        echo "Citation '$CITE' missing" 1>&2
      }
    done < <(echo "$CITES")

    # Check for non-citation warnings
    NONCIT=$(echo "$WARNINGS" | grep -v 'Citation `'                      |
                                grep -v "There were undefined citations." |
                                grep -v "Citation(s) may have changed."   |
                                grep -v "Rerun to get cross-references right.")
    [[ -z "$NONCIT" ]] || {
      echo "$NONCIT" 1>&2
      echo "There were warnings from the renderer" 1>&2
    }
    mkdir "$out"
  '';

  checkPageCount = runCommand "check-page-count"
    {
      inherit render;
      buildInputs  = [ poppler_utils ];
      FIDDLESOURCE = "${wrap {
        name   = "disable-appendices";
        script = ''
          #!/usr/bin/env bash
          set -e

          # Disables appendices, so we can count pages without them
          F=appendices.tex

          [[ -e "$F" ]] || {
            echo "No '$F' found in '$PWD', aborting" 1>&2
            exit 1
          }

          # Rather than deleting stuff, we wrap in an '\iffalse' LaTeX block
          {
            echo
            echo '\iffalse'
            echo
            cat "$F"
            echo
            echo '\fi'
            echo
          } > temp
          mv temp "$F"
        '';
      }}";
    }
    ''
      echo "Checking page count, without appendices" 1>&2

      "$render" > /dev/null || {
        echo "Couldn't render without appendices" 1>&2
        exit 1
      }

      PAGES=$(pdfinfo src/report.pdf | grep Pages | grep -o "[0-9]*$")
      ALLOWED=15
      if [[ "$PAGES" -gt "$ALLOWED" ]]
      then
        echo "report.pdf should have $ALLOWED pages, instead has $PAGES" 1>&2
        echo "(not including appendices)"                                1>&2
        exit 1
      else
        echo "Page target is $ALLOWED, you have $PAGES (without appendices)!" 1>&2
      fi
      mkdir "$out"
  '';
}
