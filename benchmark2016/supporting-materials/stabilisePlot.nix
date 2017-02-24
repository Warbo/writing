with builtins;
with import ./stabiliseUtils.nix;
pkgs.runCommand "stabilisePlot"
  {
    quickSpecData = quickSpec.data;
       mlSpecData = mlSpec.data;
    quickSpecBars = plotsOf "quickSpec" quickSpec.data;
       mlSpecBars = plotsOf    "mlSpec"    mlSpec.data;
  }
  ''
    mkdir "$out"
    cp -r "$quickSpecData" "$out/quickSpecData.json"
    cp -r    "$mlSpecData" "$out/mlSpecData.json"
    cp -r "$quickSpecBars" "$out/quickSpecStability.png"
    cp -r    "$mlSpecBars" "$out/mlSpecStability.png"
  ''
