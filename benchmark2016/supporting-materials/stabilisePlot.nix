with builtins;
with rec {
  pkgs = import <nixpkgs> {};

  inherit (pkgs)
    buildEnv callPackage jq lib makeWrapper pythonPackages runCommand stdenv
    writeScript;

  inherit (lib)
    range stringToCharacters take toInt;

  inherit (callPackage ./drawStabilisePlots.nix {})
    chartsOf plotTests;

  haskell-te = import (pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "ceb50a6";
    sha256 = "0xvjnxkn7y4wx5ij1jzcwi1v476iz6z7y4c81gpnx1y34cj1iki1";
  });

  getData = cmd: setup: pkgs.stdenv.mkDerivation {
    # Forces tests to be run before we spend ages getting the data
    inherit plotTests;
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te jq ];
    buildCommand = ''
      ${setup}
      export EXPLORATION_MEM=3000000
      MAX_SECS=600 SAMPLE_SIZES="5 10 15 100" REPS=30 ${cmd} | jq -s '.' > "$out"
    '';
  };

  quickSpec = rec {
    data = getData "quickspecBench" "";
  };

  mlSpec = rec {
    data = getData "mlspecBench" ''
      export JVM_OPTS="-Xmx168m -Xms168m -XX:PermSize=32m -XX:MaxPermSize=32m -Xss1m"
    '';
  };
};

pkgs.runCommand "stabilisePlot"
  {
    quickSpecData = quickSpec.data;
       mlSpecData = mlSpec.data;
    quickSpecBars = chartsOf "quickSpec" quickSpec.data;
       mlSpecBars = chartsOf    "mlSpec"    mlSpec.data;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData" "$out/quickSpecData.json"
    cp -r    "$mlSpecData" "$out/mlSpecData.json"
    cp -r "$quickSpecBars" "$out/quickSpecStability.png"
    cp -r    "$mlSpecBars" "$out/mlSpecStability.png"
  ''
