with { resources = import ../resources; };
with resources.nixpkgs-joined;
with rec {
  tex = texlive.combine { inherit (texlive) scheme-small; };

  src = ./machinelearning.tex;

  # Narrow down our huge Bibtex file to just the things we reference
  bib = runCommand "bibtex.bib"
    {
      inherit src;
      inherit (resources) bibtex;
      buildInputs = [ bibtool tex ];
    }
    ''
      ln -s "$src"    article.tex
      ln -s "$bibtex" bibtex.bib

      pdflatex article

      bibtool -x article.aux -o NewBib.bib

      mv NewBib.bib "$out"
    '';

  # The main rendered output
  pdf = runCommand "article.pdf"
    {
      inherit bib src;
      buildInputs = [ tex ];
    }
    ''
      ln -s "$src" article.tex
      ln -s "$bib" bibtex.bib

      function go {
        echo "Running pdflatex" 1>&2
        pdflatex article
      }

      go
      go
      #echo "Running bibtex" 1>&2
      #bibtex article
      go
      mv article.pdf "$out"
    '';

  dir = {
    "article.tex" = src;
    "article.pdf" = pdf;
    "bibtex.bib"  = bib;
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

      for F in article.tex article.pdf bibtex.bib
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
