{ fail, lib, nixListToBashArray, runCommand }:

with builtins;
with lib;
with rec {
  isTex = path: hasSuffix ".tex" (baseNameOf path);

  texFiles = filterSource (path: type: isTex path) ./..;
};
{
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
          if grep -v 'newcommand' < "$F" | grep "\\$CMD[^{]"
          then
            FAIL=1
            echo "Spotted unbraced $CMD in $(basename "$F")" 1>&2
          fi
        done < <(grep 'newcommand{' < "$header" | cut -d '{' -f2-  |
                                                  cut -d '}' -f1   |
                                                  grep -v 'argmin' |
                                                  grep -v '^\\C'   )
      done
      [[ "$FAIL" -eq 0 ]] || fail "Macros should end in {} for whitespace"
      mkdir "$out"
    '';
}
