with builtins;
with {
  inherit (import ../resources) bibtex nixpkgs-joined styles;
};
with nixpkgs-joined;
with lib;
with rec {
  inherit (callPackage ./supporting-material {}) graphs;

  render = wrap {
    name  = "render-bucketing-paper";
    paths = [
      gnumake
      (texlive.combine {
        inherit (texlive) scheme-small tikzinclude tikz-qtree algorithmicx
          algorithm2e algorithms;
      })
    ];
    vars = {
      inherit bibtex;

      go = wrap {
        name   = "go";
        script = ''
          pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report
        '';
      };

      source = filterSource (path: _: hasSuffix ".tex" path ||
                                      hasSuffix ".cls" path)
                            ./.;

      styles = concatStringsSep " " (attrValues styles);
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      cp -r "$source" ./src
      chmod -R +w     ./src
      cp "$bibtex"    ./Bibtex.bib

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
};
rec {
  #inherit graphs;

  checks = callPackage ./check.nix { inherit bibtex render; };

  paper = runCommand "bucketing.pdf" { inherit render; } ''
    "$render"
    mkdir "$out"
    mv src/report.pdf "$out"/
  '';
}
