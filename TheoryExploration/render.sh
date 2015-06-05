#!/bin/sh
nix-shell --pure --show-trace --command "sh" <<EOF
  echo "Works"
  #ARGS="--filter panpipe --filter panhandle" PATTERN="notes" renderWatch md2pdf
EOF
