with rec {
  pkgs = import <nixpkgs> {};

  haskell-te = import (pkgs.fetchFromGitHub {
    owner  = "Warbo";
    repo   = "haskell-te";
    rev    = "06de48e";
    sha256 = "1zh2mnwwhli2zb0qd13pjh234sw45r1sh4r5mm6zp1xsnyq1f7pi";
  });

  getData = cmd: pkgs.stdenv.mkDerivation {
    name = "${cmd}-stabilise-data";
    buildInputs  = [ haskell-te ];
    buildCommand = ''
      SAMPLE_SIZES="5 10 15" REPS=30 ${cmd} > "$out"
    '';
  };

  quickSpec = rec {
    data = getData "quickspecBench";
  };

  mlSpec = rec {
    data = getData "mlspecBench";
  };
};

pkgs.runCommand "stabilisePlot"
  {
    quickSpecData = quickSpec.data;
    mlSpecData    = mlSpec.data;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData" "$out/quickSpecData.json"
    cp -r "$mlSpecData"    "$out/mlSpecData.json"
  ''
