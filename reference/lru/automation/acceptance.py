"""Frozen execution checks; universal correctness also requires independent audit."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1'}


def main():
    lock = json.loads((ROOT / 'upstream.lock.json').read_text())
    upstream = ROOT / 'vendor/go_freelru'
    for name, digest in lock['files'].items():
        p = upstream / name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            raise SystemExit('Upstream integrity failed: ' + name)
    for name in ('PROOF.bend', 'tools/validate.py', 'END_TO_END.bend'):
        if not (ROOT / name).is_file():
            raise SystemExit('INCOMPLETE: missing ' + name)
    report = ROOT / 'build/validation.json'
    report.parent.mkdir(exist_ok=True)
    report.unlink(missing_ok=True)
    commands = [
        ['/Users/monkeair/.bend/bin/bend', 'PROOF.bend'],
        [sys.executable, 'tools/validate.py', '--report', str(report)],
        ['/Users/monkeair/.bend/bin/bend', 'END_TO_END.bend'],
    ]
    for command in commands:
        print('CHECK:', command, flush=True)
        result = subprocess.run(command, cwd=ROOT, env=ENV)
        if result.returncode:
            raise SystemExit(result.returncode)
    expected = sorted(x['name'] for x in json.loads((ROOT / 'tests.manifest.json').read_text()))
    rows = json.loads(report.read_text())['upstream_cases']
    if sorted(x['name'] for x in rows) != expected or any(x['status'] != 'passed' for x in rows):
        raise SystemExit('All inventoried single-threaded upstream tests must pass uniquely')
    # The auditor checks actual test execution, independent reference semantics,
    # universal theorem meaning, composition, and public implementation linkage.


if __name__ == '__main__':
    main()
