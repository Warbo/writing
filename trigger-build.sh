#!/usr/bin/env bash
set -e

# Trigger a build on Laminar continuous integration server.

# This can be useful as a post-commit hook for working copies, to check that
# local changes build correctly. It could also be used as a post-receive hook on
# a central repository, to perform the "real" build, but warbo-utilities has a
# more generic post-receive.hook.remote which can do the job better.
if command -v laminarc > /dev/null
then
  echo "Queueing laminar build" 1>&2
  LAMINAR_REASON="Git commit" laminarc queue writing
else
  echo "Skipping laminar build, laminarc not found" 1>&2
fi
