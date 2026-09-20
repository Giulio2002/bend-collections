#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: sh automation/restart.sh PREVIOUS_RUN' >&2
  exit 2
fi
cd /Users/monkeair/work/lru-bend
unset NO_COLOR
export TERM=xterm-256color COLORTERM=truecolor FORCE_COLOR=1 BEND_NO_TELEMETRY=1
export PATH="/Users/monkeair/.bend/bin:/Users/monkeair/.bun/bin:/Users/monkeair/.local/bin:/opt/homebrew/bin:$PATH"
exec /Users/monkeair/auto-implementer/.venv/bin/python automation/start_from_session.py "$1"
