# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

{ nixpkgs }:

with builtins;
with nixpkgs.repo1609."00ef7f9";
rec {
  # All definitions; useful for debugging
  graphs = callPackage ./graphs.nix {};

  # Journal of Automated Reasoning LaTeX files, from
  # http://www.springer.com/cda/content/document/cda_downloaddocument/?SGWID=0-0-45-468198-0
  latex = ./LaTeX.zip;
}
