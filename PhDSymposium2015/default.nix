with { inherit (import ../resources) bibtex nixpkgs-joined; };
with nixpkgs-joined;

runCommand "phd-symposium-2015"
  {
    buildInputs = [
      pandocPkgs
      (texlive.combine {
        inherit (texlive) helvetic scheme-small;
      })
    ];
  }
  ''
    ln -s "${./acm_proc_article-sp.cls}" ./acm_proc_article-sp.cls
    ln -s "${./acm-sig-proceedings.csl}" ./acm-sig-proceedings.csl
    ln -s "${./sig-alternate.cls}"       ./sig-alternate.cls
    ln -s "${./templates}"               ./templates
    ln -s "${./resources}"               ./resources
    ln -s "${bibtex}"                    ./Bibtex.bib

    mkdir "$out"

    echo "Rendering slides" 1>&2
    pandoc -w dzslides --standalone --self-contained \
           --filter pandoc-citeproc -o "$out/slides.html" "${./slides.md}"

    echo "Rendering abstract" 1>&2
    pandoc --data-dir="$PWD" \
           --template=default.latex \
           -o "$out/abstract.pdf" \
           -N "${./abstract.md}"
  ''
