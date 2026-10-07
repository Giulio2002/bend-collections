#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
bend=${BEND:-$(python3 - "$root/tools/toolchain.json" <<'PY'
import json
import os
import sys

with open(sys.argv[1], encoding="utf-8") as file:
    print(os.path.expanduser(json.load(file)["binary"]))
PY
)}
bend=$(command -v "$bend") || { echo "Bend compiler not found; set BEND" >&2; exit 2; }
bend=$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$bend")

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

check() {
  local label=$1 ref=$2 fixture=$3
  if ! git -C "$root" cat-file -e "${ref}^{commit}"; then
    echo "Missing $ref; use a full clone or fetch that commit" >&2
    exit 2
  fi
  mkdir -p "$tmp/$label"
  git -C "$root" archive "$ref" | tar -x -C "$tmp/$label"
  cp "$root/tests/consumer_api/$fixture" "$tmp/$label/consumer.bend"
  echo "Checking $label source ($ref)"
  (cd "$tmp/$label" && BEND_NO_TELEMETRY=1 "$bend" consumer.bend --check-only)
}

check current HEAD current.bend
check published-1.0.0.0 8e660ee published-1.0.0.0.bend
