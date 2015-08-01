#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash -p md2pdf

function go {
    ARGS="--filter pandoc-citeproc" md2pdf
}

go

if [ "x$1" = "xloop" ]
then
    while true
    do
        sleep 2
        go
    done
fi
