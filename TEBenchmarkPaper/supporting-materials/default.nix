# Data, figures, etc. for use in the paper. These are spread out over multiple
# files; here we select the high-level, "final results" which are used when
# rendering.

with builtins;

rec {
  # All definitions; useful for debugging
  debug = rec {

    # General utilities, etc. including nixpkgs and haskell-te
    defs = import ./defs.nix;
    inherit (defs) callPackage attrsToDir;
  };

  # Journal of Automated Reasoning LaTeX files, from
  # http://www.springer.com/cda/content/document/cda_downloaddocument/?SGWID=0-0-45-468198-0
  latex = ./LaTeX.zip;
}
