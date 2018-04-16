{ docsOnly ? true }:

with { defs = rec {
  abstract =
    with pkgs // {
      render = "pdflatex -interaction=nonstopmode -halt-on-error abstract";
    };
    runCommand "phd-symp-2018-abstract.pdf"
      {
        buildInputs = [ tex ];
        src = attrsToDirs {
          "abstract.tex"            = ./abstract.tex;
          "acm_proc_article-sp.cls" = ./acm_proc_article-sp.cls;
          "acm-sig-proceedings.csl" = ./acm-sig-proceedings.csl;
          "Bibtex.bib"              = resources.bibtex;
          "default.cls"             = ./default.cls;
          "sig-alternate.cls"       = ./sig-alternate.cls;
        };
      }
      ''
        cp -s "$src"/* ./
        ${render}
        bibtex abstract
        ${render}
        ${render}
        mv abstract.pdf "$out"
    '';

  both = pkgs.attrsToDirs {
    "abstract.pdf" = abstract;
    "slides.pdf"   = slides;
  };

  pkgs = resources.nixpkgs.repo1709."809056c";

  resources = import ../resources;

  slides = pkgs.nothing;

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  tex = with pkgs; texlive.combine {
    inherit (texlive)
      algorithmicx algorithm2e algorithms collection-fontsrecommended
      collection-fontsextra csvsimple csquotes frankenstein helvetic
      latex-fonts multirow paralist psnfss scheme-small tikzinclude tikz-qtree
      type1cm;
  };
}; };

if docsOnly
   then defs.both
   else defs
