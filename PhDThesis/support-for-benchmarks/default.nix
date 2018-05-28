# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ chosenPkgs, bibtex, tex, textWidth }:

with builtins;
with chosenPkgs;
rec {
  graphs = callPackage ./graphs.nix { inherit tex textWidth; };

  comparison = callPackage ./comparison.nix {
    inherit (graphs) isacosyData quickspecData;
  };

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  /*tex = (texlive.combine {
    inherit (texlive)
    csvsimple scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e
    algorithms enumitem frankenstein csquotes multirow type1cm;
  });*/
}
