{ basicTex, data, lib, python3, runCommand, writeScript }:

with builtins;
with lib;
rec {
  # TODO: Does this exist in nixpkgs somewhere? If not, move to nix-helpers
  foldAttrs = f: init: attrs: fold (name: f name (getAttr name attrs))
                                   init
                                   (attrNames attrs);

  processSamples = {name, samples}: rec {
    inherit name samples;

    names = foldAttrs (size: reps: got:
                        foldAttrs (rep: data: got:
                                    unique (got ++ data.sample))
                                  got
                                  reps)
                      []
                      samples;

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
                            samples;

    counts = listToAttrs (map (name: { inherit name; value = count name; })
                              names);

    # (Names of) definitions which only appear in failed samples
    toxic = filter (name: (count name).successes == 0) names;

    # Decoded, human-readable version of the toxic names. These names also
    # contain the TIP filename they appear in, so we can look up their
    # definitions.
    readableToxic = map deHex toxic;

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
        buildInputs = [ basicTex (python3.withPackages (p: [ p.matplotlib ])) ];
        script      = ./contentsGraph.py;
      }
      ''
        mkdir "$out"
        cd "$out"
        "$script"
      '';
  };

  all = processSamples { name = "all"; samples = data.data.result; };

  # Analyses only those samples which don't contain toxic definitions
  nonToxic = processSamples {
    name    = "nontoxic";
    samples = detox all.toxic data.data.result;
  };

  # Decodes a hex-encoded name like 'global0123456789abcdef'
  deHex = s:
    with rec {
      suffix = substring 6 (stringLength s) s;

      getPairs = x: with { l = stringLength x; };
                    if l < 2
                       then []
                       else [(substring 0 2 x)] ++ getPairs (substring 2 l x);

      pairs = getPairs suffix;

      digits = { "0" = 0 ; "1" = 1 ; "2" = 2 ; "3" = 3; "4" = 4; "5" = 5; "6" = 6;
                 "7" = 7 ; "8" = 8 ; "9" = 9 ; "a" = 10;  "b" = 11;  "c" = 12;
                 "d" = 13; "e" = 14; "f" = 15; };

      decode = pair:
        with rec {
          high  = getAttr (substring 0 1 pair) digits;
          low   = getAttr (substring 1 2 pair) digits;
          n     = (high * 16) + low;
          str   = toString n;
          upper = n > 64 && n < 91;
          lower = n > 96 && n < 123;
          digit = n > 47 && n < 58;
          other = { "46" = "."; "47" = "/"; "95" = "_"; };
        };
        if upper
           then elemAt upperChars (n - 65)
           else if lower
                   then elemAt lowerChars (n - 97)
                   else if digit
                           then toString (n - 48)
                           else if hasAttr str other
                                   then getAttr str other
                                   else abort "Unknown char ${str}";

      chars = map decode pairs;
    };
    concatStringsSep "" chars;

  # Filters out samples containing toxic names
  detox = toxic:
    with { containsFailure = rep: any (n: elem n rep.sample) toxic; };
    mapAttrs (_: filterAttrs (_: rep: !(containsFailure rep)));
}
