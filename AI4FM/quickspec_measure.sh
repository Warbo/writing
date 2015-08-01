#! /usr/bin/env nix-shell
#! nix-shell -i bash -p QuickSpecMeasure bash

i=0
while true
do
    echo "SIZE $i"
    env time -f "%e" QuickSpecMeasure "$i" 2>&1
    i=$(($i + 1))
done
