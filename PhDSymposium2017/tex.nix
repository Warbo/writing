{ texlive }:

texlive.combine {
  inherit (texlive)
    scheme-small tikzinclude tikz-qtree algorithmicx algorithm2e algorithms
    frankenstein csquotes helvetic paralist;
}
