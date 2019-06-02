with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs;
with rec {
  tex = texlive.combine {
    inherit (texlive)
      beamer collection-basic collection-latex
      collection-latexrecommended enumitem

      # These come from generic-recommended (maybe not all needed)
      apnum epsf fontname genmisc kastrup multido path tex-ps ulem;
  };
};
runCommand "ai4fm"
  {
    inherit bibtex;
    __noChroot  = true;
    src         = ./.;
    buildInputs = [ ditaa pandocPkgs tex ];
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
