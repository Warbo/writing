with builtins;
with {
  inherit (import ../../resources) bibtex nixpkgs styles;
};
with nixpkgs;
with lib;
rec {
  # External repos, which contain useful data

  # Implements hashspec (pseudorandom) and MLSpec (recurrent clustering)
  bucketingSrc = fetchgit {
    url    = http://chriswarbo.net/git/bucketing-algorithms.git;
    rev    = "9c13a24";
    sha256 = "0z0b4534a5ziyw3486x9y7vqp6jnv53dg6axygzdnv77qmfy6fka";
  };

  bucketing = import "${bucketingSrc}";

  # Implements wrappers around QuickSpec 1 and contains runtime benchmarks
  inherit (bucketing) haskellTE haskellTESrc;

  # Raw and analysed data
  data     = callPackage ./data.nix     { inherit haskellTESrc;  };
  contents = callPackage ./contents.nix { inherit basicTex data; };
  toxic    = callPackage ./toxic        {
    inherit haskellTE;
    inherit (contents.all) readableToxic;
  };

  survivalAnalysis = callPackage ./survival.nix { inherit basicTex; };
  allSurvival      = survivalAnalysis { data  = data.data.result;
                                        label = "all"; };
  nontoxicSurvival = survivalAnalysis { data  = contents.nontoxic.samples;
                                        label = "nontoxic"; };

  # Extract graphs from the above analyses
  graphs = callPackage ./graphs.nix   { inherit bucketing; };
  images = runCommand "bucketing-images"
    {
      ds = [
        contents.all.proportions
        contents.nontoxic.proportions
        allSurvival.survivalGraph
        allSurvival.timeoutGraph
        nontoxicSurvival.survivalGraph
        nontoxicSurvival.timeoutGraph
      ];
    }
    ''
      mkdir "$out"
      for D in $ds
      do
        find "$D" -type f | while read -r F
        do
          NAME=$(basename "$F")
          cp -v "$F" "$out/$NAME"
        done
      done
    '';

  # Just enough LaTeX packages to render PDF graphs
  basicTex = texlive.combine { inherit (texlive) scheme-small; };

  # All of the LaTeX and related tools for rendering the paper
  fullTex  = buildEnv {
    name = "bucketing-tex";
    paths = [
      pythonPackages.pygments  # For minted
      which                    # For minted
      (texlive.combine {
        inherit (texlive)
          algorithm2e
          algorithmicx
          algorithms
          framed      # Required by minted
          fvextra     # Required by minted
          ifplatform  # Required by minted
          minted      # Code listings
          scheme-small
          tikzinclude
          tikz-qtree
          xstring     # Required by minted
          ;
      })
    ];
  };

  render = wrap {
    name  = "render-bucketing-paper";
    paths = [ fullTex gnumake ];
    vars  = {
      inherit bibtex images;

      go = wrap {
        name   = "go";
        script = ''
          #!/usr/bin/env bash
          set -e
          echo "Running pdflatex" 1>&2
          pdflatex -interaction=nonstopmode \
                   -halt-on-error \
                   --shell-escape report || {
            echo "ERROR: pdflatex gave error code $?" 1>&2
            exit 1
          }
        '';
      };

      source = filterSource (path: _: hasSuffix ".tex" path ||
                                      hasSuffix ".cls" path)
                            ./..;

      styles = concatStringsSep " " (attrValues styles);
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      cp -r "$source" ./src
      chmod -R +w     ./src
      cp     "$bibtex" ./src/Bibtex.bib
      cp -rL "$images" ./src/images

      for STYLE in $styles
      do
        cp "$STYLE" ./src
      done

      cd ./src
      [[ -z "$FIDDLESOURCE" ]] || $FIDDLESOURCE

      "$go"
      echo "RUNNING bibtex"
      bibtex report
      "$go"
      "$go"
    '';
  };

  #inherit graphs;

  checks = callPackage ./check.nix { inherit bibtex render; };

  paperUntested = runCommand "bucketing-paper" { inherit render; } ''
    "$render"
    mkdir "$out"
    mv src/report.pdf "$out"/
  '';

  paper = withDeps (allDrvsIn checks) paperUntested;
}
