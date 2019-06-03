{ die, haskellPackages, lib, runCommand, wrap }:

with lib;
with rec {
  lines  = splitString "\n" (readFile ../../background_quickcheck.tex);

  # Given sentinel 'foo' returns alines between '% BEGIN foo' and '% END foo'.
  # The first and last lines of the result are discarded (we assume they're
  # \begin{haskell} and \end{haskell}) and the remaining are concatenated.
  chop = sentinel:
    with rec {
      begin = "% BEGIN ${sentinel}";
      end   = "% END ${sentinel}";

      dropPrefix = lines:
        if lines == []
           then die { inherit begin; error = "Sentinel not found"; }
           else if head lines == begin
                   then tail lines
                   else dropPrefix (tail lines);

      dropSuffix = acc: lines:
        if lines == []
           then die { inherit end; error = "Sentinel not found"; }
           else if head lines == end
                   then acc
                   else dropSuffix (acc ++ [ (head lines) ])
                                   (tail lines);
    };
    concatStringsSep "\n"
      (tail (init (dropSuffix [] (dropPrefix lines))));

  runner = { sentinel, tests }: runCommand "quickcheck-${sentinel}" {} (wrap {
    name   = "quickchecker-${sentinel}";
    paths  = [ (haskellPackages.ghcWithPackages (h: [
                 h.directory h.QuickCheck ])) ];
    script = ''
      #!/usr/bin/env runhaskell
      import System.Directory
      import System.Environment
      import Test.QuickCheck

      ${if sentinel == "unit" then "" else chop "abs"}

      ${chop sentinel}

      main = do
        ${concatMapStringsSep " >> " (t: "quickCheck " + t) tests}
        getEnv "out" >>= createDirectory
    '';
  });
};
mapAttrs (sentinel: tests: runner { inherit sentinel tests; }) {
  unit         = [ "fact_base" "fact_increases" "fact_div"            ];
  neg          = [                                         "fact_neg" ];
  quickchecked = [ "fact_base" "fact_increases" "fact_div" "fact_neg" ];
}
