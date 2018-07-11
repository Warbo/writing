with { inherit (import ../resources) bibtex nixpkgs warbo-packages; };
with nixpkgs.repo1609."00ef7f9";
with rec {
  # Take TeX from 1703
  tex = with nixpkgs.repo1703."de1ceec"; texlive.combine {
    inherit (texlive)
      beamer collection-basic collection-genericrecommended collection-latex
      collection-latexrecommended enumitem;
  };
};
runCommand "ai4fm"
  {
    inherit bibtex;
    src         = ./.;
    buildInputs = [ ditaa warbo-packages."c2ea27d".pandocPkgs tex ];
  }
  ''
    set -e

    # Slides
    pandoc -w dzslides --standalone --self-contained --mathml \
           -o "$PWD/slides.html" --filter=pandoc-citeproc --filter=panpipe \
           --filter=panhandle "$src/slides.md"

    # Article
    cp -r "$src" ./src
    chmod +w -R  ./src
    cp "$bibtex"   src/Bibtex.bib
    pushd src
      latex article
      bibtex article
      latex article
      pdflatex article
    popd

    mkdir "$out"
    cp slides.html "$out"/
    cp ./src/article.pdf "$out"/
  ''
