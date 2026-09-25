"""The pinned Bend toolchain (tools/toolchain.json).

Set BEND_HOME to a directory holding .bend/bin/bend and .bend/bend2 to use a
private copy of the pinned release (the binary reads Base from $HOME/.bend);
otherwise the paths in toolchain.json are used.

Set BEND to another compiler (a path, or a name on the PATH) to use it instead
of the pin; BEND_BASE may name its base.bend. PINNED is then False, and the
scripts that check the pin warn instead of failing.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / 'tools' / 'toolchain.json').read_text())
HOME = os.environ.get('BEND_HOME')
OVERRIDE = os.environ.get('BEND')
PINNED = not OVERRIDE
if OVERRIDE:
    BEND = shutil.which(os.path.expanduser(OVERRIDE)) or os.path.expanduser(OVERRIDE)
    BASE = os.path.expanduser(os.environ.get('BEND_BASE', LOCK['base']))
    ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1'}
    print('toolchain: BEND=%s overrides the pinned %s' % (BEND, LOCK['version']), file=sys.stderr)
elif HOME:
    BEND = str(Path(HOME) / '.bend' / 'bin' / 'bend')
    BASE = str(Path(HOME) / '.bend' / 'bend2' / 'base.bend')
    ENV = {**os.environ, 'HOME': HOME, 'BEND_NO_TELEMETRY': '1'}
else:
    BEND = os.path.expanduser(LOCK['binary'])
    BASE = os.path.expanduser(LOCK['base'])
    ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1'}

def version(bend, env=None):
    """The compiler's version: releases answer --version, newer builds `version`."""
    for flag in ('--version', 'version'):
        p = subprocess.run([bend, flag], capture_output=True, text=True, env=env)
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    return 'unknown'

VERSION = LOCK['version'] if PINNED else version(BEND, ENV)
