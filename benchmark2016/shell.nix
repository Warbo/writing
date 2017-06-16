with import <nixpkgs> {};
runCommand "benchmark-paper-env"
  { inherit (import ./supporting-materials) buildInputs; }
  "exit 1"
