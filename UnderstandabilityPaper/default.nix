with { resources = import ../resources; };
with resources.nixpkgs-joined;
with rec {
  render = ''
    echo "Running pdflates (1)" 1>&2
    pdflatex article

    echo "Running bibtex" 1>&2
    bibtex   article

    if [[ -e article.bbl ]]
    then
      echo "Generated 'article.bbl'" 1>&2
    else
      fail "No 'article.bbl' produced"
    fi

    echo "Running pdflates (2)" 1>&2
    pdflatex article

    echo "Running pdflates (3)" 1>&2
    pdflatex article
  '';

  tex = texlive.combine { inherit (texlive) scheme-small; };

  src = ./machinelearning.tex;

  bib = ./biblio.bib;

  # The main rendered output
  pdf = runCommand "article.pdf"
    {
      inherit bib src;
      buildInputs = [ tex ];
    }
    ''
      ln -s "$src" article.tex
      ln -s "$bib" biblio.bib

      function check {
        if grep 'LaTeX Warning: Citation'
        then
          fail "Missing citations"
        fi
      }

      ${render} 2>&1 | check

      mv article.pdf "$out"
    '';

  dir = {
    "article.tex" = src;
    "article.pdf" = pdf;
    "biblio.bib"  = bib;
  };

  archive = runCommand "article.zip"
    {
      content     = attrsToDirs' "article" dir;
      buildInputs = [ zip ];
    }
    ''
      # Chase down symlink targets
      cp -rL "$content" article

      # Zip up the actual files, rather than symlinks
      zip -r "$out" article
    '';

  check = runCommand "article-check"
    {
      inherit archive;
      buildInputs = [ fail unzip ];
    }
    ''
      unzip "$archive"
      [[ -d article ]] || {
        find . 1>&2
        fail "Didn't make 'article' dir"
      }

      for F in article.tex article.pdf biblio.bib
      do
        [[ -f article/"$F" ]] || {
          find .
          fail "Didn't make 'article/$F'"
        }
      done

      echo pass > "$out"
    '';

  checked = withDeps [ check ] archive;
};

attrsToDirs' "machine-learning-section" (dir // {
  "article.zip" = checked;
})
