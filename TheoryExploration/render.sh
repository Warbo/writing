#!/bin/sh
nix-shell -E 'with import <nixpkgs> {}; callPackage ./. {}' \
          --show-trace --command "bash" <<'EOF'
  for src in *.md
  do
    doc=$(basename "$src" .md)
    echo "Rendering $doc"
    pandoc --filter panpipe --filter panhandle -o "$doc.pdf" "$doc.md"
  done
EOF
