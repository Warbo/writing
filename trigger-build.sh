#!/usr/bin/env bash
# Trigger a build on Laminar continuous integration server. Useful as a git hook
# for both post-commit (to check that local changes work) and post-receive (to
# perform the "real" build).
if command -v laminarc > /dev/null
then
  echo "Queueing laminar build" 1>&2
  LAMINAR_REASON="Git commit" laminarc queue writing
else
  echo "Skipping laminar build, laminarc not found" 1>&2
fi
