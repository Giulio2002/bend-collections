#!/bin/sh
set -eu
if tmux has-session -t dsa-auto 2>/dev/null; then
  echo 'dsa-auto already exists; attach with: tmux attach -t dsa-auto'
  exit 1
fi
tmux new-session -d -s dsa-auto -n implementer /Users/monkeair/work/bend-dsa/automation/run.sh
echo 'Started. Attach with: tmux attach -t dsa-auto'
