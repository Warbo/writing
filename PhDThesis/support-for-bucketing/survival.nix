# Perform survival rate analysis for QuickCheck running times
{ basicTex, buildPackages, callPackage, fetchurl, gcc, lib, libgccFix,
  nixpkgs1709, overrideCC, path, python3, python3Packages, runCommand, runner,
  stdenv, textWidth, wrap, writeScript }:

with builtins;
with lib;

{ data, label }: rec {
  times = mapAttrs (_: mapAttrs (_: rep: {
                     inherit (rep) success;
                     time = if rep.success
                               then rep.time
                               else rep.timeout;
                   }))
                   data;

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
    entry = size: rep: data: [
      (size + "_" + rep)
      size
      (toString data.time)
      (fromBool data.success)
    ];

    fromBool  = b: if b then "1" else "0";

    processed = mapAttrs (size: mapAttrs (entry size)) times;

    headers   = [ "id" "size" "time" "success" ];

    tabulated = concatLists (map attrValues (attrValues processed));

    commaSep  = concatStringsSep ",";

    lineSep   = concatStringsSep "\n";

    rows      = [ (commaSep headers) ] ++ map commaSep tabulated;

    csv       = writeScript "qs-times.csv" (lineSep rows);
  };

  survivalGraph = runCommand "survival-graph"
    {
      inherit label textWidth;
      inherit (timingCsv) csv;
      buildInputs = [ basicTex ];
      script      = wrap {
        name  = "survivalGraph.py";
        file  = ./survivalGraph.py;
        paths = [ (python3.withPackages (p: [ lifelines ])) ];
      };
    }
    runner;

  timeoutGraph = runCommand "timeout-graph"
    {
      inherit label textWidth;
      inherit (timingCsv) csv;
      buildInputs = [ basicTex ];
      script = wrap {
        name  = "timeoutGraph.py";
        file  = ./timeoutGraph.py;
        paths = [ (python3.withPackages (p: [ p.matplotlib p.scipy ])) ];
      };
    }
    runner;
}
