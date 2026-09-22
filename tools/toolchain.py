"""The pinned Bend toolchain (tools/toolchain.json).

Set BEND_HOME to a directory holding .bend/bin/bend and .bend/bend2 to use a
private copy of the pinned release (the binary reads Base from $HOME/.bend);
otherwise the paths in toolchain.json are used.
"""
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / 'tools' / 'toolchain.json').read_text())
HOME = os.environ.get('BEND_HOME')
if HOME:
    BEND = str(Path(HOME) / '.bend' / 'bin' / 'bend')
    BASE = str(Path(HOME) / '.bend' / 'bend2' / 'base.bend')
    ENV = {**os.environ, 'HOME': HOME, 'BEND_NO_TELEMETRY': '1'}
else:
    BEND = LOCK['binary']
    BASE = LOCK['base']
    ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1'}
