{ bash, mkBin, perl, runCommand, tetex }:

runCommand "tetex-hack"
  {
    inherit tetex;
    newDvipng = mkBin {
      name   = "dvipng";
      paths  = [ perl tetex ];
      script = ''
        #!${bash}/bin/bash
        set -e
        if [[ "x$1" = "x-version" ]]
        then
          dvipng "$@" | perl -pe 's/[^[:ascii:]]//g'
        else
          dvipng "$@"
        fi
      '';
    };
  }
  ''
    set -e

    # Hack for https://github.com/matplotlib/matplotlib/issues/4545/
    mkdir -p "$out/bin"
    for F in "$tetex/bin"/*
    do
      cp -s "$F" "$out/bin"/
    done
    rm "$out/bin/dvipng"
    ln -s "$newDvipng/bin/dvipng" "$out/bin/dvipng"
  ''
