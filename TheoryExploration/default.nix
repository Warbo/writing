with builtins;
with { inherit (import ../resources) nixpkgs-joined; };
with nixpkgs-joined;
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
