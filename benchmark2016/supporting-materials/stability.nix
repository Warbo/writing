{ buildEnv, callPackage, haskell-te, haskell-te-defs, haskell-te-src, jq, lib,
  makeWrapper, miller, pythonPackages, runCommand, sampledBenchmarkData, stdenv,
  writeScript }:

with builtins;
with lib;
rec {
  stabilityPlots = mapAttrs plotsOf sampledBenchmarkData;

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

    plot =
    with {
      env = with pythonPackages; python.buildEnv.override rec {
        extraLibs = [ numpy matplotlib pillow scipy ];
      };
    };
    runCommand "chart.py"
      {
        buildInputs = [ makeWrapper env ];
        plotter     = writeScript "plotter.py" (readFile ./plotter.py);
      }
      ''
        mkdir -p "$out/bin"
        makeWrapper "$plotter" "$out/bin/plot" --prefix PATH : "${env}/bin"
      '';

  plotsOf = name: data:
    stdenv.mkDerivation {
      name         = "barchart-${name}";
      buildInputs  = [ plot ];
      buildCommand = ''
        mkdir -p "$out/charts"
        cp "${data}" "$out/data.json"
        cd "$out/charts"
        echo "Plotting charts for ${data}" 1>&2
        plot < ../data.json
      '';
    };

  plotTests = stdenv.mkDerivation {
    name = "plot-tests";
    src  =
      # Generate some semi-plausible data to test with
      with rec {
        data = runCommand "test-data.json" { buildInputs = [ jq ]; } ''
          jq 'map(. + {"results": (.results | map(. + {
                         "precision" : (.precision | tonumber),
                         "recall"    : (.recall    | tonumber)
                       }))})' < "${rawData}" > "$out"
        '';

        rawData    = writeScript "raw-data.json" (toJSON [correlated uniform]);

        correlated = {
          info    = 1;
          results = map (n: {
                          time      = (2 * n) + 3;
                          failure   = if elem n [3 8]
                                         then n + 20
                                         else null;
                          precision = "0." + toString n;
                          recall    = "0." + toString (n * 2);
                        })
                        (range 1 30);
        };

        uniform = {
          info    = 2;
          results = map (n: {
                          time      = randomise n;
                          failure   = if elem n [3 8]
                                         then n + 20
                                         else null;
                          precision = "0." + toString (randomise (n * 127));
                          recall    = "0." + toString (randomise (n * 131));
                        })
                        (range 1 30);
        };

        randomise = n:
          with rec {
            # Generate digits uniformly, by taking a hash and discarding a-f
            hash   = hashString "sha256" (toString n);
            digits = stringToCharacters "1234567890";
            valid  = filter (c: elem c digits) (stringToCharacters hash);
          };
          # Append digits, just in case we hit a purely alphabetical hash ;)
          toInt (concatStringsSep "" (take 5 (valid ++ digits)));
      };
      plotsOf "test" data;

    doCheck    = true;
    checkPhase = ''
      echo "Testing plots from $src" 1>&2
      for SET in 1 2
      do
        for F in bars lag acorr
        do
          [[ -f "$src/charts/$F-$SET.png" ]] || {
            echo "Missing $F charts for $SET" 1>&2
            exit 1
          }
        done
      done
    '';
    installPhase = ''
      echo 'true' > "$out"
    '';
  };
}
