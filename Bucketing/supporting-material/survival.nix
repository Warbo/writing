# Perform survival rate analysis for QuickCheck running times
{ callPackage, data, fetchurl, lib, nixpkgs1609, path, python3, python3Packages,
  runCommand, stdenv, overrideCC, buildPackages }:

with builtins;
with lib;
rec {
  # Pandas is marked as broken on i686, and the "bail out if marked as broken"
  # mechanism is so strict that this can't be overridden without causing a bail
  # out. To avoid this we make our own copy of the pandas derivation and patch
  # it to remove the broken annotation. We also disable the "installCheck" phase
  # since it tries to call pytest with unrecognised arguments.
  pandas = rec {
    def = runCommand "pandas.nix"
      rec {
        f = path + "/pkgs/development/python-modules/pandas/default.nix";

        pattern = ''pname = "pandas";'';
        replace = pattern + concatStrings [ "doCheck = false;"
                                            "doInstallCheck = false;"
                                            ''installCheckPhase = "true";'' ];
      }
      ''
        grep -v 'broken *=' < "$f" | sed -e "s/$pattern/$replace/g" > "$out"
      '';
    drv = callPackage def {
      inherit (patchedPackages)
        beautifulsoup4 bottleneck buildPythonPackage cython dateutil fetchPypi
        html5lib lxml moto numexpr openpyxl pytest pytz scipy sqlalchemy tables
        xlrd xlwt;
    };
  };

  # There is a bug in i686 nixpkgs which causes errors like:
  #   ImportError:
  #   /nix/store/...-scipy-1.1.0/.../_sparsetools.cpython-36m-i386-linux-gnu.so:
  #   undefined symbol: __divmoddi4
  # This is caused by the wrong GCC being used, affecting many packages (Qt,
  # spidermonkey, etc.). Until it's fixed upstream (which hasn't happened as of
  # nixpkgs18.09) the workaround is to override the C compiler in stdenv.
  # See https://github.com/NixOS/nixpkgs/issues/36947
  python3Patched = python3.override {
    stdenv = overrideCC stdenv buildPackages.gcc6;
  };

  # We need to override all of the Python packages we use, so that they use the
  # patched version of Python
  patchedPackages = python3Packages.override { python = python3Patched; };

  lifelines = patchedPackages.buildPythonPackage rec {
    name = pname;
    pname = "lifelines";
    version = "0.19.0";

    src =
      with { repo = "https://github.com/CamDavidsonPilon"; };
      fetchurl {
        url    = "${repo}/${pname}/archive/v${version}.tar.gz";
        sha256 = "1vdpa8jfcjc5isv2bgq96jslkh430b0c5pigs0fy9asa1wk3019i";
      };

    propagatedBuildInputs = with patchedPackages; [
      autograd
      bottleneck
      matplotlib
      pandas.drv
      pytest
      scipy
    ];

    #doCheck = false;
  };

  survivalGraph = runCommand "survival-graph.png"
    {
      buildInputs = [ (python3.withPackages (p: [ p.pandas])) ];
      script      = ./survivalGraph.py;
    }
    ''
      "$script"
    '';
}
