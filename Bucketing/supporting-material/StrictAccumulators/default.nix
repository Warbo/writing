{ buildEnv, haskellPackages }: rec {

  env = buildEnv {
    name  = "strict-accumulator-env";
    paths = [
      (haskellPackages.ghcWithPackages (h: [ h.quickspec ]))
    ];
  };
}
