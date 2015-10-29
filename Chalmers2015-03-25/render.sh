#! /usr/bin/env nix-shell
#! nix-shell -i bash -p pandoc panpipe panhandle

pandoc -t beamer -o slides.pdf slides.md
