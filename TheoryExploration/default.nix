with builtins;
with rec {
  inherit ((import ../resources).nixpkgs.repo1609.ffa6543)
    haskellPackages lib pandoc panhandle panpipe runCommand texlive withNix;
};
with lib;
with rec {
  notes  = filter (hasSuffix ".md") (attrNames (readDir ./.));
  nameOf = removeSuffix ".md";
  pdfOf  = file: (nameOf file) + ".pdf";
  render = file: runCommand  "theory-exploration-notes-${pdfOf file}"
    (withNix {
      src         = ./. + "/${file}";
      buildInputs = [
        pandoc
        haskellPackages.pandoc-citeproc
        panpipe
        panhandle
        (texlive.combine { inherit (texlive) scheme-small; })
      ];
    })
    ''
      pandoc --filter panpipe --filter panhandle -o "$out" "$src"
    '';
};
listToAttrs (map (file: { name = nameOf file; value = render file; }) notes)
