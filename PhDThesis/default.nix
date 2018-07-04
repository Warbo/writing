with builtins;
with { inherit (import ../resources) bibtex nixpkgs; };
with { chosenPkgs = nixpkgs.repo1609."00ef7f9"; };
with chosenPkgs;
with lib;
with { defs = rec {
  inherit bibtex;

  tex = (texlive.combine {
    inherit (texlive)
      csquotes csvsimple enumitem scheme-small tikzinclude type1cm;
  });

  isTex = path: hasSuffix ".tex" (baseNameOf path);

  render = { env ? {}, file, label ? "default", src }:
    runCommand "${file}-${label}.pdf"
      (env // {
        inherit file src;
        buildInputs = [ tex ];
      })
      ''
        function go {
          pdflatex -interaction=nonstopmode -halt-on-error --shell-escape "$@"
        }

        echo "SRC is '$src'" 1>&2
        cp -s  "$src"/*  ./
        ${env.commands or ""}

        go     "$file"
        [[ -e "Bibtex.bib" ]] && bibtex "$file"
        go     "$file"
        go     "$file"

        cp "$file.pdf" "$out"
      '';

  benchmarkSupport = callPackage ./support-for-benchmarks {
    inherit bibtex chosenPkgs tex textWidth;
  };

  # Render a "dummy" version of the thesis which has all of the same styling
  # but just spits out the text width to stdout. We capture this and write
  # it to a file, so the figure generators can read it and set the correct
  # size, without having to scale things up or down.
  textWidth = runCommand "widthTex"
    {
      real        = filterSource (path: type: isTex path) ./.;
      buildInputs = [ tex ];
    }
    ''
      cp -r "$real" ./src
      chmod +w -R   ./src
      pushd ./src > /dev/null
        cat "${./header}"                                  \
            <(echo '\typeout{WIDTH \the\textwidth WIDTH}') \
            "${./footer}"                                  > ./thesis.tex

        echo "THESIS CONTENT" 1>&2
        cat ./thesis.tex 1>&2
        echo "END THESIS CONTENT" 1>&2

        pdflatex -interaction=nonstopmode -halt-on-error thesis | tee out ||
          true

        grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' < ./out |
          sed -e 's/WIDTH//g'                      |
          tr -d 'pt ' > "$out"
      popd > /dev/null
    '';

  renderSection = file:
    assert pathExists (./. + "/${file}.tex") || abort "'${file}.tex' not found";
    render {
      inherit file;
      src  = filterSource (path: type: isTex path) ./.;
      env  = {
        commands = with benchmarkSupport; with comparison; ''
          for D in "${graphs.graphs}" "${qualityComparison}" "${timeComparison}"
          do
            echo "Putting '$D' in place" 1>&2
            cp -rs "$D"/* ./
          done

          ln -sv "${bibtex}" ./Bibtex.bib

          echo "Splicing header and footer into '$file'" 1>&2
          cat "${./header}" "$file.tex" "${./footer}" > TEMP
          mv TEMP "$file.tex"
        '';
      };
    };

  outline = render {
    file = "outline";
    src  = attrsToDirs { outline = ./outline.tex; };
  };

  thesis = renderSection "thesis";

  pdfs = attrsToDirs {
    "outline.pdf" = outline;
    "thesis.pdf"  = thesis;
  };

}; };

{ pdfOnly ? true }: if pdfOnly then defs.pdfs else defs
