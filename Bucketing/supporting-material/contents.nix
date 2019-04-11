{ data, lib, python3, runCommand, tex, writeScript }:

with builtins;
with lib;
rec {
  # TODO: Does this exist in nixpkgs somewhere? If not, move to nix-helpers
  foldAttrs = f: init: attrs: fold (name: f name (getAttr name attrs))
                                   init
                                   (attrNames attrs);

  names = foldAttrs (size: reps: got:
                      foldAttrs (rep: data: got:
                                  unique (got ++ data.sample))
                                got
                                reps)
                    []
                    data.data.result;

  count = name: foldAttrs (size: reps: got:
                            foldAttrs (rep: data: got:
                                        if elem name data.sample
                                           then {
                                             successes =
                                               if data.success
                                                  then (got.successes + 1)
                                                  else got.successes;
                                             fails =
                                               if data.success
                                                  then got.fails
                                                  else (got.fails + 1);
                                           }
                                           else got)
                                      got
                                      reps)
                          { successes = 0; fails = 0; }
                          data.data.result;

  counts = listToAttrs (map (name: { inherit name; value = count name; })
                            names);

  tabulated = foldAttrs (name: { fails, successes }: got: got ++ [
                          [ name (toString successes) (toString fails) ]
                        ])
                        [ [ "name" "successes" "failures" ] ]
                        counts;

  csv = writeScript "qs-contents"
                    (concatStringsSep "\n"
                      (map (concatStringsSep ",") tabulated));

  proportions = runCommand "content-failure-proportions"
    {
      inherit csv;
      buildInputs = [ (python3.withPackages (p: [ p.matplotlib ])) tex ];
      script      = ./contentsGraph.py;
    }
    ''
      mkdir "$out"
      cd "$out"
      "$script"
    '';
}
