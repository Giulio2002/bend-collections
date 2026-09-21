#!/usr/bin/env python3
"""Development helper: time one (structure, op, size) row outside the gate.

  python3 tools/dev/quick_bench.py prefix_trie 3 0 200000 [reps] [--src FILE]

Builds benchmarks/bend/<structure>.bend (or --src) with the pinned compiler and
benchmarks/native/<structure>.c with the gate's flags, runs both with the same
argv, and prints (A - B) / (count * reps) for each side. It uses the gate's
argv contract but none of its acceptance rules; numbers from this tool are
never evidence, only a guide for where to look.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LOCK = json.loads((ROOT / 'inventory' / 'toolchain.json').read_text())
BEND = LOCK['binary']
CFLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
TIME_RE = re.compile(r'TA=(\d+)\s+TB=(\d+)\s+TC=(\d+)')
OUT = ROOT / 'build' / 'quick'


def main():
    args = sys.argv[1:]
    src = None
    if '--src' in args:
        i = args.index('--src')
        src = args[i + 1]
        del args[i:i + 2]
    name, op, size, count = args[0], args[1], args[2], args[3]
    reps = args[4] if len(args) > 4 else '1'
    OUT.mkdir(parents=True, exist_ok=True)
    bsrc = src or 'benchmarks/bend/%s.bend' % name
    bbin = OUT / ('%s.bend.bin' % name)
    cbin = OUT / ('%s.c.bin' % name)
    p = subprocess.run([BEND, bsrc, '-o', str(bbin)], cwd=ROOT, capture_output=True, text=True)
    if not bbin.exists() or p.returncode != 0:
        sys.exit(p.stdout + p.stderr)
    subprocess.run(['cc'] + CFLAGS + ['-o', str(cbin), 'benchmarks/native/%s.c' % name], cwd=ROOT, check=True)
    n = int(count) * int(reps)
    for label, cmd, scale in [('bend', [str(bbin), '--threads', '1', '--'], 1e6), ('c', [str(cbin)], 1.0)]:
        best = None
        for order in ['0', '1', '0']:
            r = subprocess.run(cmd + [op, size, count, reps, '12345', order], cwd=ROOT, capture_output=True, text=True)
            m = TIME_RE.search(r.stdout)
            if not m:
                sys.exit('%s: no timing\n%s%s' % (label, r.stdout, r.stderr))
            d = (int(m.group(1)) - int(m.group(2))) * scale / n
            best = d if best is None else min(best, d)
        print('%-5s %10.2f ns/op' % (label, best))


if __name__ == '__main__':
    main()
