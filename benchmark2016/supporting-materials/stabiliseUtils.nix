{ haskell-te, haskell-te-defs, haskell-te-src, miller, pkgs }:

rec {
  inherit (pkgs)
    buildEnv callPackage jq lib makeWrapper pythonPackages runCommand stdenv
    writeScript;

  inherit (lib)
    mapAttrs range stringToCharacters take toInt;

  inherit (callPackage ./drawStabilisePlots.nix {})
    plotsOf plotTests plot;



  results =
    let go = cmd: let data = getData cmd; in {
          "data.json" = data;
          plots       = plotsOf cmd data;
          small       = smallTheoryData cmd;
        };
     in {
          quickSpec = go "quickspecBench";
          mlSpec    = go "mlspecBench";
          hashSpec  = go "hashspecBench";
        };

  small = mapAttrs (n: v: v.small) results;

  attrsToDirs = attrs:
    with rec {
      names     = attrNames attrs;
      dataOf    = name: attrsToDirs attrs."${name}";
      nameToCmd = name: ''
        cp -r "${dataOf name}" "$out/${name}"
      '';
      commands  = concatStringsSep "\n" (map nameToCmd names);
    };
    if attrs ? builder
       then attrs
       else stdenv.mkDerivation {
              name = "collated-data";
              buildCommand = ''
                mkdir -p "$out"
                ${commands}
              '';
            };

  collated = attrsToDirs results;

  graphed = stdenv.mkDerivation {
    inherit collated;
    name = "graphed";
    buildInputs = [ plot ];
    buildCommand = ''
      cp -r "$collated" "$out"
      chmod +w -R "$out"
      while read -r JSONFILE
      do
        SUFF=$(echo "$JSONFILE" | sed -e "s@$out/@@g")
         DIR=$(dirname "$SUFF")
        NAME=$(basename "$JSONFILE" .json)
        mkdir -p "$out/$DIR/$NAME"
        pushd "$out/$DIR/$NAME"
          plot < "$JSONFILE"
        popd
      done < <(find "$out" -name "*.json")
    '';
  };

  getStats =
    with {
      script = writeScript "getStats.py" ''
        """Given a JSON array of numbers on stdin, returns mean and stddev."""
        import json
        import numpy as np

        data = json.loads(sys.stdin.read())
        print(json.dumps({"mean"   : np.mean(data),
                          "stddev" : np.stddev(data)}))
      '';
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "stats.py" { buildInputs = [ makeWrapper ]; } ''
      makeWrapper "${script}" "$out" --prefix PATH : "${env}/bin"
    '';
}
