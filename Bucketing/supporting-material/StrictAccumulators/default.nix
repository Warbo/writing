{ attrsToDirs', buildEnv, collapseAttrs, die, dirsToAttrs, fetchFromGitHub,
  haskellTE, haskellPackages, lib, nixpkgs1803, runCommand, timeout, withDeps,
  writeScript }:

with builtins;
with lib;
rec {
  checkVersion = version:
    with { allowed = [ 1 2 ]; };
    assert elem version allowed || die {
      inherit allowed version;
      error = "Unknown QuickSpec version given";
    };
    version;

  getVersion = version: getAttr (toString (checkVersion version));

  env = version: getVersion version {
    "1" = buildEnv {
      name  = "ghc-with-quickspec1";
      paths = [
        (haskellTE.haskellPackages.ghcWithPackages (h: [ h.quickspec ]))
      ];
    };

    "2" =
      with rec {
        # Version 2 of QuickSpec
        src = fetchFromGitHub {
          owner  = "nick8325";
          repo   = "quickspec";
          rev    = "464e0c6";
          sha256 = "0j9n7jvx555lrz53p4cdmqwzpwksi6yn2d7pf4apd3qiwlsyaqcj";
        };

        # Pick some of the provided examples, to check that QS2 is working. We
        # don't want all of them, since some take ages.
        examples = filterAttrs
          (n: v: elem n [ "Arith.hs" "Bool.hs" ])
          (collapseAttrs (dirsToAttrs "${src}/examples"));

        haskellPackagesWithQuickSpec2 = haskellPackages.override (old: {
          overrides = helf: huper: {
            quickspec =
              with rec {
                nixed = helf.haskellSrc2nix {
                  inherit src;
                  name = "quickspec";
                };

                untested = helf.callPackage nixed {};

                runExamples = mapAttrs
                  (n: f: runCommand "quickspec-example-${n}"
                    {
                      inherit f;
                      buildInputs = [ (helf.ghcWithPackages (h: [
                        (h.callPackage nixed {})
                      ])) ];
                    }
                    ''runhaskell "$f" > "$out"'')
                  examples;
              };
              withDeps (attrValues runExamples) untested;

            # Needed for QuickSpec, but isn't in the 18.03 cabal snapshot
            twee-lib = helf.callPackage
              (nixpkgs1803.haskellPackages.hackage2nix "twee-lib" "2.1.5")
              {};
          };
        });
      };
      buildEnv {
        name  = "ghc-with-quickspec2";
        paths = [
          (haskellPackagesWithQuickSpec2.ghcWithPackages (h: [
            h.quickspec
          ]))
        ];
      };
    };

  run = { version, name }: runCommand "quickspec-run-${name}"
    {
      # Settings for timeout
      MAX_SECS = "300";
      MAX_KB   = "1000000";

      buildInputs = [ (env version) timeout ];
      code        = attrsToDirs' "quickspec-code-${name}" {
        "Defs.hs"    = ./Defs.hs;
        "Runners.hs" = getVersion version {
          "1" = ./QS1Runners.hs;
          "2" = abort "FIXME: No QS2 runner yet";
        };
        "Main.hs"    = writeScript "run-${name}.hs" ''
          module Main where
          import qualified Runners
          main = Runners.${name}
        '';
      };
    }
    ''
      cp -r "$code" ./code
      chmod -R +w   ./code
      cd            ./code
      ghc --make -o Main Main.hs
      withTimeout ./Main
    '';
}
