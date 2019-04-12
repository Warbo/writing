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

  # Data for graphs, etc.

  data = callPackage ./data.nix { inherit haskellTESrc; };

  survival = callPackage ./survival.nix {
    inherit data;
    tex = texlive.combine { inherit (texlive) scheme-small; };
  };

  graphs = callPackage ./graphs.nix {};

  strictAccumulators = callPackage ./StrictAccumulators { inherit haskellTE; };

  images = runCommand "bucketing-images"
    {
      ds = [
        survival.contents.proportions
        survival.survivalGraph
        survival.timeoutGraph
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

  render = wrap {
    name  = "render-clustering-paper";
    paths = [
      gnumake
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
    vars = {
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
      cp    "$bibtex" ./src/Bibtex.bib
      cp -r "$images" ./src/images

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

  paperUntested = runCommand "clustering-paper" { inherit render; } ''
    "$render"
    mkdir "$out"
    mv src/report.pdf "$out"/
  '';

  paper = withDeps (allDrvsIn checks) paperUntested;
}
