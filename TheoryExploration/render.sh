#!/bin/sh
nix-shell --pure --show-trace --command "sh" <<'EOF'
  for src in *.md
  do
    doc=$(basename "$src" .md)
    echo "Rendering $doc"
    pandoc --filter panpipe --filter panhandle -o "$doc.pdf" "$doc.md"
  done
EOF
