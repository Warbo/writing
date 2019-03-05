with { resources = import ../resources; };
with resources.nixpkgs-joined;
with rec {
  render = ''
    echo "Running pdflates (1)" 1>&2
    pdflatex iccc-science

    echo "Running bibtex" 1>&2
    bibtex   iccc-science

    if [[ -e iccc-science.bbl ]]
    then
      echo "Generated 'iccc-science.bbl'" 1>&2
    else
      fail "No 'iccc-science.bbl' produced"
    fi

    echo "Running pdflates (2)" 1>&2
    pdflatex iccc-science

    echo "Running pdflates (3)" 1>&2
    pdflatex iccc-science
  '';

  tex = texlive.combine { inherit (texlive) scheme-small; };

  src = ./iccc-science.tex;

  bib = ./biblio.bib;

  # The main rendered output
  pdf = runCommand "iccc-science.pdf"
    {
      inherit bib src;
      buildInputs = [ tex ];
    }
    ''
      ln -s "$src" iccc-science.tex
      ln -s "$bib" biblio.bib

      function check {
        if grep 'LaTeX Warning: Citation'
        then
          fail "Missing citations"
        fi
      }

      ${render} 2>&1 | check

      mv iccc-science.pdf "$out"
    '';

  dir = {
    "iccc-science.tex" = src;
    "iccc-science.pdf" = pdf;
    "biblio.bib"       = bib;
  };

  archive = runCommand "iccc-science.zip"
    {
      content     = attrsToDirs' "iccc-science" dir;
      buildInputs = [ zip ];
    }
    ''
      # Chase down symlink targets
      cp -rL "$content" submit

      # Zip up the actual files, rather than symlinks
      zip -r "$out" submit
    '';

  check = runCommand "submit-check"
    {
      inherit archive;
      buildInputs = [ fail unzip ];
    }
    ''
      unzip "$archive"
      [[ -d submit ]] || {
        find . 1>&2
        fail "Didn't make 'submit' dir"
      }

      for F in article.tex iccc-science.pdf biblio.bib
      do
        [[ -f submit/"$F" ]] || {
          find .
          fail "Didn't make 'submit/$F'"
        }
      done

      echo pass > "$out"
    '';

  checked = withDeps [ check ] archive;
};

attrsToDirs' "iccc-science" (dir // {
  "submit.zip" = checked;
})
