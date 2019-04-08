# Perform survival rate analysis for QuickCheck running times
{ callPackage, data, fetchurl, gcc, lib, nixpkgs1709, path, python3,
  python3Packages, runCommand, stdenv, overrideCC, buildPackages, writeScript }:

with builtins;
with lib;
rec {
  # Pandas is marked as broken on i686, and the "bail out if marked as broken"
  # mechanism is so strict that this can't be overridden without causing a bail
  # out. To avoid this we make our own copy of the pandas derivation and patch
  # it to remove the broken annotation. We also disable the "installCheck" phase
  # since it tries to call pytest with unrecognised arguments.
  pandas =
    with {
      def = runCommand "pandas.nix"
        rec {
          f = path + "/pkgs/development/python-modules/pandas/default.nix";

          pattern = ''pname = "pandas";'';
          replace = concatStrings [ pattern
                                    ''name = "pandas";''
                                    "doCheck = false;"
                                    "doInstallCheck = false;"
                                    ''installCheckPhase = "true";'' ];
        }
        ''
          grep -v 'broken *=' < "$f" | sed -e "s/$pattern/$replace/g" |
            sed -e 's/inherit (stdenv) isDarwin;/isDarwin = false;/g' > "$out"
        '';
    };
    callPackage def {
      inherit (python3Packages)
        beautifulsoup4 bottleneck buildPythonPackage cython dateutil fetchPypi
        html5lib lxml moto numexpr openpyxl pytest pytz scipy sqlalchemy tables
        xlrd xlwt;
    };

  # There is a bug in i686 nixpkgs which causes errors like:
  #   ImportError:
  #   /nix/store/...-scipy-1.1.0/.../_sparsetools.cpython-36m-i386-linux-gnu.so:
  #   undefined symbol: __divmoddi4
  # This is caused by the wrong GCC being used, affecting many packages (Qt,
  # spidermonkey, etc.). Until it's fixed upstream (which hasn't happened as of
  # nixpkgs18.09) the workaround is to add a version of libgcc_s.so.1 to the
  # LD_LIBRARY_PATH.
  # See https://github.com/NixOS/nixpkgs/issues/36947
  libgccFix = ''
    echo "Looking for libgcc" 1>&2
    FOUND=0
    for F in "${gcc.cc.lib}"/lib/libgcc_s.so.*
    do
      FOUND=1
      echo "Forcing LD_LIBRARY_PATH to use '$F'" 1>&2
      D=$(dirname "$F")
      export LD_LIBRARY_PATH="$D:$LD_LIBRARY_PATH"
    done
    if [[ "$FOUND" -eq 0 ]]
    then
      echo "Failed to find libgcc_s.so" 1>&2
      exit 1
    fi
  '';

  # The lifelines library performs survival analysis
  lifelines =
    with {
      pyPkgs = python3Packages // { inherit pandas; };
    };
    pyPkgs.buildPythonPackage rec {
      name    = pname;
      pname   = "lifelines";
      version = "0.19.3";

      src =
        with { repo = "https://github.com/CamDavidsonPilon"; };
        fetchurl {
          url    = "${repo}/${pname}/archive/v${version}.tar.gz";
          sha256 = "1xpc5p9rv4sa9g1m05ra50z2mbxrwr090l9yjq3lnbj8b1snw8dg";
        };

      propagatedBuildInputs = with pyPkgs; [
        autograd
        bottleneck
        matplotlib
        pandas
        pytest
        scipy
      ];

      preCheck = libgccFix;
    };

  timingCsv = rec {
    fromBool = b: if b then "1" else "0";

    entry = size: rep: data: [
      (size + "_" + rep)
      size
      (toString data.time)
      (fromBool data.success)
    ];

    processed =  mapAttrs (size: mapAttrs (entry size))
                          data.times;

    headers   = [ "id" "size" "time" "success" ];

    tabulated = concatLists (map attrValues (attrValues processed));

    commaSep  = concatStringsSep ",";

    lineSep   = concatStringsSep "\n";

    rows      = [ (commaSep headers) ] ++ map commaSep tabulated;

    csv       = writeScript "qs-times.csv" (lineSep rows);
  };

  # Runs $script to put stuff in $out
  runner = ''
    ${libgccFix}
    mkdir "$out"
    cd "$out"
    "$script"
  '';

  survivalGraph = runCommand "survival-graph"
    {
      inherit (timingCsv) csv;
      buildInputs = [ (python3.withPackages (p: [ lifelines ])) ];
      script      = ./survivalGraph.py;
    }
    runner;

  timeoutGraph = runCommand "timeout-graph"
    {
      inherit (timingCsv) csv;
      buildInputs = [
        (python3.withPackages (p: [
          p.matplotlib
          p.scipy
          #(python3Packages // { inherit pandas; }).pandas
        #  lifelines
        ]))
        #(python3.withPackages (p: [ lifelines ]))
      ];
      script      = ./timeoutGraph.py;
    }
    runner;
}
