#!/bin/sh
nix-shell --pure --command 'ARGS="--template=./templates/default.latex" OPTIONS=pp md2pdf'
