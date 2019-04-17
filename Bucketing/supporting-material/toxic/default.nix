{ attrsToDirs', buildEnv, collapseAttrs, die, dirsToAttrs, fetchFromGitHub,
  haskellTE, haskellPackages, isBroken, lib, nixpkgs1803, readableToxic,
  runCommand, time, timeout, withDeps, writeScript }:

with builtins;
with lib;
assert with {
         stripPath = n: last (splitString "/" n);
         got  = sort (x: y: x < y) (map stripPath readableToxic);
         want = [ "mult2" "mul3" "mul3acc" "op" "qexp" ];
       };
       got == want || die {
         inherit got readableToxic want;
         error = "Toxic names don't match those in our experiments";
       };
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
                nixed = nixpkgs1803.haskellPackages.haskellSrc2nix {
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
      MAX_KB   = "2000000";


      # Output format
      TIME = ''{"wall-clock":%e,"cpu-time":%U,"max-resident-kB":%M}'';

      buildInputs = [ (env version) time timeout ];
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
      time -f "$TIME" withTimeout ./Main 2>&1 | tee output
      mv output "$out"
    '';

  runs =
    with rec {
      breaks = drv: trace "FIXME: Uncomment to confirm failures" /*withDeps [ (isBroken drv) ]*/
                             (writeScript "failed" "failed");

      # Which definitions are broken with which generators
      broken = {
        small = [ "qexp_lazy" ];
      };

      go1 = name: {
        inherit name;
        value = {
          big    = {
            lazy   = breaks (run { version = 1; name = "qs_${name}_lazy";   });
            strict = breaks (run { version = 1; name = "qs_${name}_strict"; });
          };
          small = {
            lazy   = with {
                       x = run { version = 1; name = "small_${name}_lazy"; };
                     };
                     if elem (name + "_lazy") broken.small
                        then breaks x
                        else x;
            strict = run { version = 1; name = "small_${name}_strict"; };
          };
        };
      };

      names = [ "mult2" "op" "qexp" ];
    };
    attrsToDirs' "problematic-quickspec-definitions" {
      quickspec1 = listToAttrs (map go1 names);
    };
}
