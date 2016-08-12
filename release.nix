with import <nixpkgs> {};
{
  ML4HSTechReport = stdenv.mkDerivation {
    name = "ml4hs-tech-report";
    src  = ./ML4HSTechReport;
    buildCommand = ''
      source $stdenv/setup

      make

      cp report.pdf "$out"
    '';
  };

  theoryExploration = import ./TheoryExploration;

}
