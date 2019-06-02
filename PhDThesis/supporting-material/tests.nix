{ asBashArray, callPackage, fail, importFrom, lib, nixListToBashArray,
  runCommand }:

with builtins;
with lib;
with rec {
  isTex = path: hasSuffix ".tex" (baseNameOf path);

  texFiles = filterSource (path: type: isTex path) ./..;
};
mapAttrs (_: f: callPackage f {}) (importFrom ./tests) // {
  everything-included = runCommand "everything-included"
    {
      inherit texFiles;
      buildInputs = [ fail ];
    }
    ''
      for F in "$texFiles"/*.tex
      do
        N=$(basename "$F")

        # Skip auxilliary files
        [[ "x$N" = "xoutline.tex" ]] && continue

        # Skip top-level (it won't be included by anything else)
        [[ "x$N" = "xthesis.tex" ]] && continue

        echo "Looking for '$N'" 1>&2
        grep -R "\\input{$N}" "$texFiles" || fail "File '$N' isn't included"
      done
      mkdir "$out"
    '';

  no-bare-macros = runCommand "no-bare-macros"
    {
      inherit texFiles;
      buildInputs = [ fail ];
      header      = ../header;
    }
    ''
      FAIL=0
      for F in "$texFiles"/*.tex
      do
        while read -r CMD
        do
          if grep -v 'newcommand' < "$F" | grep "\\$CMD[^{]"    |
                                           grep -v '\\hipspec{' |
                                           grep -v '\\hipster{'
          then
            FAIL=1
            echo "Spotted unbraced $CMD in $(basename "$F")" 1>&2
          fi
        done < <(grep 'newcommand{' < "$header" | cut -d '{' -f2-     |
                                                  cut -d '}' -f1      |
                                                  grep -v 'argmin'    |
                                                  grep -v '^\\C'      |
                                                  grep -v '^\\i[A-Z]' |
                                                  grep -v '^\\t[A-Z]' )
      done
      [[ "$FAIL" -eq 0 ]] || fail "Macros should end in {} for whitespace"
      mkdir "$out"
    '';

  no-unmacroed-terms = runCommand "no-unmacroed-terms"
    {
      inherit texFiles;
      buildInputs = [ fail ];
    }
    ''
      TERMS=${asBashArray [
        # These terms should be written with macros, not raw
        "hackage"
        "hipspec"
        "hipster"
        "isacosy"
        "isascheme"
        "ml4hs"
        "mlspec"
        "quickcheck"
        "quickspec"
        "speculate"
        "smallcheck"
      ]}
      EXCEPTIONS=${asBashArray [
        # Exceptions to our macros, e.g. in comments and references
        "% "
        "(hackage)"
        "(mlspec)"
        "/ml4hsfe"
        "QuickSpecExample.hs"
        "\cite{Hipster"
        "\cite{quickcheck"
        "\input{"
        "\lazysmallcheck"
        "braquehais2017speculate"
        "cite{QuickSpec"
        "claessen2011quickcheck"
        "fig:"
        "hackage.haskell.org"
        "johansson2009isacosy"
        "mlspec-helper"
        "mlspeclabel"
        "of=hackage"
        "of=mlspec"
        "quickSpec nat"
        "reverse/QuickCheck"
        "runciman2008smallcheck"
        "sec:mlspec"
        "sec:quickcheck"
      ]}
      FAIL=0
      for F in "$texFiles"/*.tex
      do
        echo "$F" | grep outline.tex > /dev/null && continue  # Skip outline
        for TERM in "''${TERMS[@]}"
        do
          # See if this TERM appears in file F, without being a macro
          if GOT=$(grep -i "[^\\]$TERM" < "$F")
          then
            # Skip if this is an allowed exception
            ALLOWED=0
            for EXCEPTION in "''${EXCEPTIONS[@]}"
            do
              echo "$GOT" | grep "$EXCEPTION" > /dev/null && ALLOWED=1
            done
            [[ "$ALLOWED" -eq 1 ]] && continue

            FAIL=1
            NAME=$(basename "$F")
            echo "$GOT" 1>&2
            echo "Spotted '$TERM', which should be a macro, in $NAME" 1>&2
          fi
        done
      done
      [[ "$FAIL" -eq 0 ]] ||
        fail "Terms written directly, when macros should be used"
      mkdir "$out"
    '';
}
