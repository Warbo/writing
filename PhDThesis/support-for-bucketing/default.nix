{ textWidth }:
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

  # There is a bug in i686 nixpkgs which causes errors like:
  #   ImportError:
  #   /nix/store/...-scipy-1.1.0/.../_sparsetools.cpython-36m-i386-linux-gnu.so:
  #   undefined symbol: __divmoddi4
  # This is caused by the wrong GCC being used, affecting many packages (Qt,
  # spidermonkey, etc.). Until it's fixed upstream (which hasn't happened as of
  # nixpkgs18.09) the workaround is to add a version of libgcc_s.so.1 to the
  # LD_LIBRARY_PATH.
  # See https://github.com/NixOS/nixpkgs/issues/36947
  libgccFix = ''
    echo "Looking for libgcc" 1>&2
    FOUND=0
    for F in "${gcc.cc.lib}"/lib/libgcc_s.so.*
    do
      FOUND=1
      echo "Forcing LD_LIBRARY_PATH to use '$F'" 1>&2
      D=$(dirname "$F")
      export LD_LIBRARY_PATH="$D:$LD_LIBRARY_PATH"
    done
    if [[ "$FOUND" -eq 0 ]]
    then
      echo "Failed to find libgcc_s.so" 1>&2
      exit 1
    fi
  '';

  # Runs $script to put stuff in $out
  runner = ''
    ${libgccFix}
    mkdir "$out"
    cd "$out"
    "$script"
  '';

  # Raw and analysed data
  graphs   = callPackage ./graphs.nix {
    inherit basicTex bucketing runner textWidth;
  };
  data     = callPackage ./data.nix     { inherit haskellTESrc;  };
  contents = callPackage ./contents.nix { inherit basicTex data; };
  toxic    = callPackage ./toxic        {
    inherit haskellTE;
    inherit (contents.all) readableToxic;
  };
  survivalAnalysis = callPackage ./survival.nix {
    inherit basicTex libgccFix runner textWidth;
  };
  allSurvival      = survivalAnalysis { data  = data.data.result;
                                        label = "all"; };
  nontoxicSurvival = survivalAnalysis { data  = contents.nontoxic.samples;
                                        label = "nontoxic"; };

  # Extract graphs from the above analyses
  images = runCommand "bucketing-images"
    {
      ds = [
        contents.all.proportions
        contents.nontoxic.proportions
        allSurvival.survivalGraph
        allSurvival.timeoutGraph
        nontoxicSurvival.survivalGraph
        nontoxicSurvival.timeoutGraph
        graphs.boundsGraph
        graphs.bucketingGraph
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
  basicTex = texlive.combine {
    inherit (texlive)
      scheme-small
      type1cm
      ucs
      ;
  };

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
          DRAFT='-draftmode'
          [[ "$FINAL" -eq 1 ]] && DRAFT=""
          echo "Running pdflatex $DRAFT" 1>&2
          pdflatex -interaction=batchmode $DRAFT \
                   -halt-on-error \
                   --shell-escape report || {
            echo "ERROR: pdflatex $DRAFT gave error code $?" 1>&2
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
      FINAL=1 "$go"
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
