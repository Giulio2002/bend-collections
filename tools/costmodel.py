#!/usr/bin/env python3
"""Cost model of the Bend native C backend against the same C primitives.

  python3 tools/costmodel.py --report build/performance/costmodel.json

Builds and runs benchmarks/micro.bend (Bend, native C backend, one thread) and
benchmarks/native/micro.c (cc -O3 -march=native), both of which perform the
identical four primitive workloads, and reports nanoseconds per primitive.

This is not one of the contract workloads: it exists so that the per-operation
ratios in BENCHMARKS.md can be read against what the primitives themselves
cost. `array` is the only primitive of the four that is competitive with C,
which is why an array-backed structure can meet the 2.5x contract and a
cons-cell or node-allocating structure cannot.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / 'inventory' / 'toolchain.json').read_text())
BEND = LOCK['binary']
CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
OUT = ROOT / 'build' / 'bench'

# operations performed by each region, identical on both sides
OPS = {'arith': 20000000, 'array': 20000000,
       'list': 4096 * 5000, 'alloc': 8191 * 5000, 'fresh': 4096 * 5000}

FIELD = re.compile(r'(\w+)_ms=([0-9.]+)')


def run(cmd):
    p = subprocess.run(cmd, cwd=str(ROOT), text=True, capture_output=True,
                       env={**os.environ, 'BEND_NO_TELEMETRY': '1'})
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', default=str(ROOT / 'build' / 'performance' / 'costmodel.json'))
    args = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)

    bb = OUT / 'micro'
    if bb.exists():
        bb.unlink()
    p = run([BEND, 'benchmarks/micro.bend', '-o', str(bb.relative_to(ROOT))])
    if not bb.exists():
        print('bend build failed:\n' + p.stdout + p.stderr, file=sys.stderr)
        return 1
    cb = OUT / 'micro_ref'
    if cb.exists():
        cb.unlink()
    p = run([CC] + CFLAGS + ['-o', str(cb.relative_to(ROOT)), 'benchmarks/native/micro.c'])
    if not cb.exists():
        print('cc build failed:\n' + p.stdout + p.stderr, file=sys.stderr)
        return 1

    pb = run([str(bb), '--threads', '1'])
    pc = run([str(cb)])
    bend = {k: float(v) for k, v in FIELD.findall(pb.stdout)}
    ref = {k: float(v) for k, v in FIELD.findall(pc.stdout)}
    if sorted(bend) != sorted(OPS) or sorted(ref) != sorted(OPS):
        print('unexpected output:\n%r\n%r' % (pb.stdout, pc.stdout), file=sys.stderr)
        return 1

    rows = []
    for name in ['arith', 'array', 'list', 'alloc', 'fresh']:
        b = bend[name] * 1e6 / OPS[name]
        c = ref[name] * 1e6 / OPS[name]
        rows.append({'primitive': name, 'operations': OPS[name],
                     'bend_ns': b, 'reference_ns': c,
                     'ratio': (b / c) if c > 0 else None})
        print('%-6s %12d ops   bend %8.2f ns   ref %8.2f ns   %8.2fx'
              % (name, OPS[name], b, c, b / c if c > 0 else float('nan')))

    rep = Path(args.report)
    rep.parent.mkdir(parents=True, exist_ok=True)
    rep.write_text(json.dumps({'primitives': rows}, indent=1, sort_keys=True))
    print('report: %s' % rep)
    return 0


if __name__ == '__main__':
    sys.exit(main())
