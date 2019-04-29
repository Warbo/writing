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
}
