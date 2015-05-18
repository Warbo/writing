#!/bin/sh
nix-shell --pure --command 'ARGS="--template=./templates/default.latex -N" OPTIONS=pp md2pdf'
