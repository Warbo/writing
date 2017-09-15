with { inherit (import ../resources) nixpkgs; };
with nixpkgs.repo1703."de1ceec";

runCommand "ai4fm.pdf"
  {
    src         = ./.;
    buildInputs = [
      (texlive.combine {
        inherit (texlive)
          beamer collection-basic collection-bibtexextra collection-binextra
          collection-context collection-fontsextra collection-fontsrecommended
          collection-fontutils collection-formatsextra collection-genericextra
          collection-genericrecommended collection-latex collection-latexextra
          collection-latexrecommended collection-mathextra collection-plainextra
          collection-pstricks collection-science; })
      gnumake bash haskellPackages.pandoc-citeproc panpipe panhandle ditaa
    ];
  }
  ''
    set -e

    # Slides
    pandoc -w dzslides --standalone --self-contained --mathml \
           -o "$PWD/slides.html --filter=pandoc-citeproc --filter=panpipe \
           --filter=panhandle "$src/slides.md"

    # Article
    cp -r "$src" ./src
    chmod +w -R ./src
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
