# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ callPackage, bibtex, nixpkgs1609, tex, textWidth }:

with builtins;
with chosenPkgs;
rec {
  graphs = callPackage ./graphs.nix {
    inherit tex textWidth;
    inherit (nixpkgs1609) python;
  };

  comparison = callPackage ./comparison.nix {
    inherit (graphs) isacosyData quickspecData;
    inherit (nixpkgs1609) python3;
  };

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  /*tex = (texlive.combine {
    inherit (texlive)
    csvsimple scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
    algorithms enumitem frankenstein csquotes multirow type1cm;
  });*/
}
