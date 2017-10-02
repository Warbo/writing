with builtins;
with rec {
  inherit ((import ../resources).nixpkgs.repo1609."00ef7f9")
    lib pandocPkgs runCommand texlive withNix;
};
with lib;
with rec {
  notes  = map (removeSuffix ".md")
               (filter (hasSuffix ".md")
                       (attrNames (readDir ./.)));
  nameOf = removeSuffix ".md";
  pdfOf  = file: file + ".pdf";
  render = file: runCommand  "theory-exploration-notes-${pdfOf file}"
    (withNix {
      src         = ./. + "/${file}.md";
      buildInputs = [
        pandocPkgs
        (texlive.combine { inherit (texlive) scheme-small; })
      ];
    })
    ''
      pandoc --filter panpipe --filter panhandle -o "$out" "$src"
    '';
};
genAttrs notes render
