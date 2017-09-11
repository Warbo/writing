{ haskellPackages, lib, pandoc, panhandle, panpipe, runCommand }:

with builtins;
with lib;
with rec {
  notes  = filter (hasSuffix ".md") (attrNames (readDir ./.));
  nameOf = removeSuffix ".md";
  pdfOf  = file: (nameOf file) + ".pdf";
  render = file: runCommand  "theory-exploration-notes-${pdfOf file}"
    {
      src         = ./. + "/${file}";
      buildInputs = [
        pandoc
        haskellPackages.pandoc-citeproc
        panpipe
        panhandle
      ];
    }
    ''
      pandoc --filter panpipe --filter panhandle -o "$out" "$src"
    '';
};
listToAttrs (map (file: { name = nameOf file; value = render file; }) notes)
