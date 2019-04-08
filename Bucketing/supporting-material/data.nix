{ haskellTESrc, jq, lib, lzip, runCommand }:

with builtins;
with lib;
rec {
  # Filenames of the haskellTE benchmark results containing our data
  dataFiles = [
    "b1247807-nix-py-dirnull.json.lz"  # Even numbered sizes
    "bdea634a-nix-py-dirnull.json.lz"  # Odd  numbered sizes
    "a531ce8f-nix-py-dirnull.json.lz"  # Rep 30
  ];

  # Extracts data from the given file and creates a .nix file for importing it
  dataFrom = file: runCommand "samples.json"
    {
      buildInputs = [ jq lzip ];
      file        = "${haskellTESrc}/benchmarks/results/desktop/${file}";
    }
    ''
      echo "Pulling samples out of '$file'" 1>&2
      mkdir "$out"
      cd "$out"
      lzip -d < "$file" | jq '.results | .["quickspectip.track_data"] |
                              .result  | .[0]                         |
                              map_values(.reps)' > data.json
      echo 'with builtins; fromJSON (readFile ./data.json)' > default.nix
    '';

  # The data read from the above files and merged together. We do this in a few
  # steps, with a bunch of assertions to check what's happened, which we collect
  # up in an attrset to avoid polluting imports with junk.
  data = rec {
    pieces = map (f: import (dataFrom f)) dataFiles;

    distinct = xs: ys: all (x: !(elem x ys)) xs && all (y: !(elem y xs)) ys;

    mergeSizes = xs: ys: ys // mapAttrs (size: reps:
                                          if hasAttr size ys
                                             then mergeReps reps (getAttr size ys)
                                             else reps)
                                        xs;

    mergeReps = xs: ys: assert distinct (attrNames xs) (attrNames ys) ||
                               abort { inherit xs ys; msg = "Reps overlap"; };
                        xs // ys;

    err = msg: abort (toJSON {
      inherit msg;
      resultUntested = substring 0 500 (toJSON resultUntested);
    });

    resultUntested = dedupeSamples (fold mergeSizes {} pieces);

    dedupeSamples = mapAttrs (_: reps:
                               fold (key: old:
                                      with {
                                        added = old // {
                                          "${key}" = getAttr key reps;
                                        };
                                      };
                                      if repsDistinct false added
                                         then added
                                         else old)
                                    {}
                                    (attrNames reps));

    allAttrs = f: a: all (n: f n (getAttr n a)) (attrNames a);

    listEqual =
      with { f = sort (x: y: x < y); };
      s1: s2: f s1 == f s2;

    sampleEqual = x: y: listEqual x.sample y.sample;

    repDistinct = die: reps: key: rep:
      all (key2: (key == key2) || !(sampleEqual rep (getAttr key2 reps)) ||
                 (if die
                     then abort (toJSON {
                                  inherit key key2;
                                  error = "Duplicate rep";
                                })
                     else false))
          (attrNames reps);

    repsDistinct = die: reps: allAttrs (repDistinct die reps) reps;

    result =
      assert all (s: with { size = toString s; };
                     hasAttr size resultUntested || err "No size ${size}")
                 (range 1 20) || err "Missing sizes";
      assert allAttrs (s: v: all (r: with { rep = toString r; };
                                     hasAttr rep v      ||
                                     elem s [ "1" "2" ] ||  # These have dupes
                                     err "Size ${s} missing rep ${rep}")
                                 (range 0 30))
                      resultUntested || err "Missing reps";
      assert allAttrs (s: allAttrs (r: y: length y.sample == fromJSON s ||
                                          err "Size ${s} rep ${r} wrong size"))
                      resultUntested || err "Wrong size sample";
      assert allAttrs (s: repsDistinct true) resultUntested;
      resultUntested;
    };

  times = mapAttrs (_: mapAttrs (_: rep: {
                                  inherit (rep) success;
                                  time = if rep.success
                                            then rep.time
                                            else rep.timeout;
                                }))
                   data.result;
}
