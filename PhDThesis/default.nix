with builtins;
with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs;
with lib;
with { defs = rec {
  inherit bibtex;

  tex = (texlive.combine {
    inherit (texlive)
      algorithm2e
      algorithmicx
      algorithms
      cm-super
      csquotes
      csvsimple
      enumitem
      framed      # Required by minted
      fvextra     # Required by minted
      ifplatform  # Required by minted
      minted      # Code listings
      multirow
      scheme-small
      tikz-qtree
      tikzinclude
      type1cm
      xpatch
      xstring     # Required by minted
      ;
  });

  renderInputs = [
    pythonPackages.pygments  # For minted
    which                    # For minted
    tex
  ];

  isTex = path: hasSuffix ".tex" (baseNameOf path);

  render = { env ? {}, file, label ? "default", src }:
    runCommand "${file}-${label}.pdf"
      (env // {
        inherit file src;
        buildInputs = renderInputs;
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
    inherit bibtex tex textWidth;
  };

  bucketingSupport = import ./support-for-bucketing { inherit textWidth; };

  # Render a "dummy" version of the thesis which has all of the same styling
  # but just spits out the text width to stdout. We capture this and write
  # it to a file, so the figure generators can read it and set the correct
  # size, without having to scale things up or down.
  textWidthDrv = runCommand "widthTex.nix"
    {
      real        = filterSource (path: type: isTex path) ./.;
      buildInputs = renderInputs;
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

        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape thesis |
          tee out || true

        N=$(grep 'WIDTH[ ]*[0-9.]*pt[ ]*WIDTH' < ./out |
              sed -e 's/WIDTH//g'                      |
              tr -d 'pt ')
        echo "\"$N\"" > "$out"
      popd > /dev/null
    '';

  # Import the textWidth derivation, to break the dependency chain between the
  # contents of the .tex files (which keep changing) and our graphs (which take
  # a while to calculate). By importing the result, we get a plain Nix string;
  # the graphs will only get rebuilt if this string's value (i.e. the text
  # width) changes; *not* if its dependencies change without affecting the
  # width (which is almost always the case)
  textWidth = import textWidthDrv;

  renderSection = file:
    assert pathExists (./. + "/${file}.tex") || abort "'${file}.tex' not found";
    render {
      inherit file;
      src  = filterSource (path: type: isTex path) ./.;
      env  = {
        commands = ''
          for D in "${benchmarkSupport.graphs.graphs}"                \
                   "${benchmarkSupport.comparison.qualityComparison}" \
                   "${benchmarkSupport.comparison.timeComparison}"
          do
            echo "Putting '$D' in place" 1>&2
            cp -rs "$D"/* ./
          done

          ln -s "${bucketingSupport.images}" ./images

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

  pdfs =
    with rec {
      mkSec  = sec: { name = "${sec}.pdf"; value = renderSection sec; };
      mkSecs = l: listToAttrs (map mkSec l);
      main   = { "outline.pdf" = outline; "thesis.pdf" = thesis; };
    };
    withDeps (allDrvsIn tests ++ [ textWidthDrv /*For the gcroot*/ ])
             (attrsToDirs (main // mkSecs [
               "appendix"
               "background"
               "benchmark"
               "bucketing"
               "clustering"
               "litreview"
               "related"
               "futurework"
             ]));

  tests = callPackage ./supporting-material/tests.nix {};

}; };

{ pdfOnly ? true }: if pdfOnly then defs.pdfs else defs
