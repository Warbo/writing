#!/usr/bin/env bash

if ! mount | grep Uni > /dev/null
then
    echo "Uni share not mounted, aborting" >> /dev/stderr
    exit 1
fi

if [[ ! -e stp  || ! -e backups ]]
then
    echo "Can't find rendered/ or backups/, aborting" >> /dev/stderr
    exit 1
fi

STAMP=$(date +%F-%H-%M-%S)
DEST="/home/chris/Uni/stp-$STAMP"
if [[ -e "$DEST" ]]
then
    echo "$DEST already exists, can't back up. Aborting" >> /dev/stderr
    exit 1
fi

if [[ -e /home/chris/Uni/stp ]]
then
    echo "Backing up to $DEST"
    mv -v /home/chris/Uni/stp "$DEST"
fi

echo "Copying rendered/stp to /home/chris/Uni/"
cp -vr rendered/stp /home/chris/Uni/
