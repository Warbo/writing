{ docsOnly ? true }:

with { defs = rec {
  abstract = graphs:
    with pkgs // {
      render = "pdflatex -interaction=nonstopmode -halt-on-error abstract";
    };
    runCommand "phd-symp-2018-abstract.pdf"
      {
        inherit graphs src;
        inherit (resources) bibtex;

        buildInputs = [ tex ];
      }
      ''
        mkdir src
        cp -s "$src"/* ./src/

        [[ -z "$graphs"            ]] || cp -rs "$graphs"/*            src/.

        ln -s "$bibtex" Bibtex.bib
        pushd src
          ${render}
          bibtex abstract
          ${render}
          ${render}
          mv abstract.pdf "$out"
        popd
    '';

  both = pkgs.attrsToDirs {
    "abstract.pdf" = abstract support.graphs.graphs;
    "slides.pdf"   = slides;
  };

  pkgs = resources.nixpkgs.repo1609."00ef7f9";

  resources = import ../resources;

  slides = pkgs.runCommand "slides.pdf"
    {
      inherit (resources) bibtex;
      buildInputs = [ pkgs.pandocPkgs tex ];
      graphs      = ./graphs;
      slides      = ./slides.md;
    }
    ''
      ln -s "$bibtex" ./Bibtex.bib
      ln -s "$graphs" ./graphs
      pandoc -t beamer --filter pandoc-citeproc -o slides.pdf "$slides"
      mv slides.pdf "$out"
    '';

  src = pkgs.attrsToDirs {
    "abstract.tex"            = ./abstract.tex;
    "acm_proc_article-sp.cls" = ./acm_proc_article-sp.cls;
    "acm-sig-proceedings.csl" = ./acm-sig-proceedings.csl;
    "default.cls"             = ./default.cls;
    "sig-alternate.cls"       = ./sig-alternate.cls;
  };

  support = import ./supporting-materials {
    inherit pkgs tex src;
    inherit (resources) bibtex;
  };

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
