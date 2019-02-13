with { inherit (import ../resources) bibtex nixpkgs-joined; };
with nixpkgs-joined;
with rec {
  abstract = graphs: runCommand "phd-symp-2018-abstract.pdf"
    {
      inherit bibtex graphs src;
      buildInputs = [ tex ];
      render      = writeScript "phdsymp18-render" ''
        pdflatex -interaction=nonstopmode -halt-on-error abstract
      '';
    }
    ''
      mkdir src
      cp -s "$src"/* ./src/

      [[ -z "$graphs" ]] || cp -rs "$graphs"/* src/

      ln -s "$bibtex" Bibtex.bib
      pushd src
        "$render"
        bibtex abstract
        "$render"
        "$render"
        mv abstract.pdf "$out"
      popd
    '';

  slides = runCommand "slides.pdf"
    {
      inherit bibtex;
      buildInputs = [ pandocPkgs tex ];
      graphs      = ./graphs;
      slides      = ./slides.md;
    }
    ''
      ln -s "$bibtex" ./Bibtex.bib
      ln -s "$graphs" ./graphs
      pandoc -t beamer --filter pandoc-citeproc -o slides.pdf "$slides"
      mv slides.pdf "$out"
    '';

  src = attrsToDirs {
    "abstract.tex"            = ./abstract.tex;
    "acm_proc_article-sp.cls" = ./acm_proc_article-sp.cls;
    "acm-sig-proceedings.csl" = ./acm-sig-proceedings.csl;
    "default.cls"             = ./default.cls;
    "sig-alternate.cls"       = ./sig-alternate.cls;
  };

  support = callPackage ./supporting-materials { inherit bibtex src tex; };

  # Provides a pdflatex binary with all packages needed by template, our
  # document and the matplotlib graphs
  tex = with pkgs; texlive.combine {
    inherit (texlive)
      algorithmicx algorithm2e algorithms collection-fontsrecommended
      collection-fontsextra csvsimple csquotes frankenstein helvetic
      latex-fonts multirow paralist psnfss scheme-small tikzinclude tikz-qtree
      type1cm;
  };
};
attrsToDirs' "phdsymp2018" {
  "abstract.pdf" = abstract support.graphs.graphs;
  "slides.pdf"   = slides;
}
