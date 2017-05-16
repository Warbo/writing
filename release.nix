with rec {
  # Use fetchgit from <nixpkgs> to get some version of nix-config
  bootPkgs = call ((import <nixpkgs> {}).fetchgit {
               url    = cfgUrl;
               rev    = "be310e2";
               sha256 = "166lzyxyh2d2ivm6bf3nrb55p00cf7q0pv1gskj8crxsx4ym8w2h";
             });

  # Use bootPkgs.latestGit to get the latest nix-config
  cfgSrc = bootPkgs.latestGit { url = cfgUrl; };

  pkgs    = call cfgSrc;

  call   = f: import "${f}" {};
  cfgUrl = http://chriswarbo.net/git/nix-config.git;

  # Evaluate and build in an isolated environment; useful for e.g. avoiding
  # problems with restricted mode on Hydra
  isolated = with pkgs; name: expr: runCommand "isolated-${name}"
    (withNix {
      inherit expr;

      HOME = runCommand "mk-home" { inherit cfgSrc; } ''
        mkdir -p "$out"
        ln -s "$cfgSrc" "$out/.nixpkgs"
      '';
    })
    ''
      nix-build --show-trace -E "$expr" -o "$out"
    '';
};
with pkgs;
{
  ML4HSTechReport   = isolated "ML4HSTechReport" ''
    with import <nixpkgs> {};
    callPackage ${./ML4HSTechReport} { bibtex = ${./Bibtex.bib}; }
  '';

  theoryExploration = isolated "TheoryExploration" ''
    with import <nixpkgs> {};
    callPackage ${./TheoryExploration} {}
  '';

  benchmark2016 = isolated "benchmark2016" "import ${./benchmark2016}";

  PhDSymposium2017  = {
    abstract = isolated "phd-symposium-2017-abstract" ''
      import ${./PhDSymposium2017}/abstract { bibtex = ${./Bibtex.bib}; }
    '';
    slides   = isolated "phd-symposium-2017-slides" ''
      import ${./PhDSymposium2017}/slides   { bibtex = ${./Bibtex.bib}; }
    '';
  };
}
