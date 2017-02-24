{ jq, lib, makeWrapper, pkgs, pythonPackages, runCommand, stdenv, writeScript }:

with builtins;
with lib;
rec {
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
      echo "Pass" > "$out"
    '';
  };
}
