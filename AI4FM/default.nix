with { inherit (import ../resources) nixpkgs; };
with nixpkgs.repo1603.configless;
stdenv.mkDerivation {
  name = "ai4fm";
  src  = ./.;
  buildDepends = [
    (texLiveAggregationFun {
       paths = [ texLive texLiveExtra texLiveFull texLiveBeamer lmodern ];
    })
  ];
  buildPhase = ''
    ./render.sh
  '';
  installPhase = ''
    mkdir "$out"
    cp *.pdf "$out/"
  '';
}
