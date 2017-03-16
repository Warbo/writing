{ jq, makeWrapper, stdenv, writeScript }:

rec {
  diffBetween = stdenv.mkDerivation {
    name = "diff-between";
    src  = writeScript "diff-between" ''
      #!/usr/bin/env bash
      set -e

      # Read in data once, so we can use process substitution when calling
      DATA1=$(cat "$1")
      DATA2=$(cat "$2")

      # Sanity check
      jq -n -e '($data1 | length) == ($data2 | length)' \
         --argfile data1 <(echo "$DATA1")               \
         --argfile data2 <(echo "$DATA2")               > /dev/null || {
        echo "Can't diff inputs of different lengths" 1>&2
        exit 1
      }

      jq -n '[range($data1 | length) | $data1[.] - $data2[.]]' \
         --argfile data1 <(echo "$DATA1")                      \
         --argfile data2 <(echo "$DATA2")
    '';

    buildInputs  = [ jq makeWrapper ];
    unpackPhase  = "true";  # Nothing to do

    doCheck    = true;
    checkPhase = ''
      function fail() {
        echo -e "FAIL: $*" 1>&2
        exit 1
      }

      if "$src" <(jq -n '[0, 1, 2]') <(jq -n '[0, 1]') 2>/dev/null
      then
        fail "Should have aborted for shorter second"
      fi

      if "$src" <(jq -n '[0, 1]') <(jq -n '[0, 1, 2]') 2>/dev/null
      then
        fail "Should have aborted for longer second"
      fi

      jq -n -e '$result == [2, 2.4, 3, 3]' \
        --argfile result <("$src" <(jq -n '[2, 3.4, 5, 7]') \
                                  <(jq -n '[0, 1,   2, 4]')) > /dev/null ||
        fail "Couldn't diff"
    '';

    installPhase = ''
      mkdir -p "$out/bin"
      makeWrapper "$src" "$out/bin/diffBetween" --prefix PATH : "${jq}/bin"
    '';
  };
}
