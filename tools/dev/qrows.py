#!/usr/bin/env python3
"""Development helper: time several rows of one structure outside the gate.

  python3 tools/dev/qrows.py bitset [--src FILE] [--csrc FILE] [--filter OPNAME] [--scale X]

Builds benchmarks/bend/<structure>.bend (or --src) and the pinned C reference
once, then times every row of that structure in benchmarks/workloads.py with
the gate's argv contract, best of three alternating runs, and prints
Bend ns/op, C ns/op and the ratio. Numbers from this tool are never evidence;
they only guide where to look. --scale multiplies the repetition count (the
default aims for ~0.2 s per region on the Bend side).
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'benchmarks'))
import workloads  # noqa: E402

LOCK = json.loads((ROOT / 'inventory' / 'toolchain.json').read_text())
BEND = LOCK['binary']
CFLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
TIME_RE = re.compile(r'TA=(\d+)\s+TB=(\d+)\s+TC=(\d+)')
OUT = ROOT / 'build' / 'quick'


def run(cmd):
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=600)
    m = TIME_RE.search(r.stdout)
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3))


def main():
    args = sys.argv[1:]
    src = filt = csrc = None
    scale = 1.0
    if '--src' in args:
        i = args.index('--src'); src = args[i + 1]; del args[i:i + 2]
    if '--csrc' in args:
        i = args.index('--csrc'); csrc = args[i + 1]; del args[i:i + 2]
    if '--filter' in args:
        i = args.index('--filter'); filt = args[i + 1]; del args[i:i + 2]
    if '--scale' in args:
        i = args.index('--scale'); scale = float(args[i + 1]); del args[i:i + 2]
    name = args[0]
    OUT.mkdir(parents=True, exist_ok=True)
    bbin = OUT / ('%s.rows.bin' % name)
    cbin = OUT / ('%s.rows.c.bin' % name)
    p = subprocess.run([BEND, src or 'benchmarks/bend/%s.bend' % name, '-o', str(bbin)], cwd=ROOT, capture_output=True, text=True)
    if p.returncode != 0 or not bbin.exists():
        sys.exit(p.stdout + p.stderr)
    subprocess.run(['cc'] + CFLAGS + ['-o', str(cbin), csrc or 'benchmarks/native/%s.c' % name], cwd=ROOT, check=True)
    rows = [w for w in workloads.TABLE if w['structure'] == name and (not filt or w['operation'].endswith('.' + filt))]
    for w in rows:
        count = w['count']
        # probe with one rep, then scale reps to ~0.2 s of Bend difference
        reps = 1
        best = {}
        for side, cmd, sc in [('bend', [str(bbin), '--threads', '1', '--'], 1e6), ('c', [str(cbin)], 1.0)]:
            r = run(cmd + [str(w['op']), str(w['size']), str(count), '1', '12345', '0'])
            if r is None:
                best[side] = None
                continue
            per = max(r[0] - r[1], 1) * sc  # ns for one rep
            reps = max(1, min(2000, int(2e8 / per * scale)))
            vals = []
            for order in ['0', '1', '0']:
                r = run(cmd + [str(w['op']), str(w['size']), str(count), str(reps), '12345', order])
                if r is None:
                    continue
                vals.append((r[0] - r[1]) * sc / (count * reps))
            best[side] = min(vals) if vals else None
        b, c = best.get('bend'), best.get('c')
        ratio = (b / c) if (b and c and c > 0) else float('nan')
        flag = '' if ratio <= 2.5 else '  <-- over'
        print('%-40s %-10s bend %10.2f  c %10.2f  %6.2fx%s' % (w['operation'], w['workload'], b or -1, c or -1, ratio, flag), flush=True)


if __name__ == '__main__':
    main()
