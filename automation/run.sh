#!/bin/sh
set -eu
cd /Users/monkeair/work/bend-dsa
unset NO_COLOR
export TERM=xterm-256color COLORTERM=truecolor FORCE_COLOR=1 BEND_NO_TELEMETRY=1
export PATH="/Users/monkeair/.bend/bin:/Users/monkeair/.bun/bin:/Users/monkeair/.local/bin:/opt/homebrew/bin:$PATH"
exec /Users/monkeair/auto-implementer/.venv/bin/auto-implementer run --objective automation/OBJECTIVE.md --policy automation/ORCHESTRATOR.MD --auditor automation/AUDITOR.md --store /Users/monkeair/auto-implementer/.autoimplementer/dsa-runs --color always --no-agent-timeouts
