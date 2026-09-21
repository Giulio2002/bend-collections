#!/usr/bin/env python3
"""Development helper: Bend driver vs C reference checksums for every row.

  python3 tools/dev/checksums.py [structure ...] [--csrc-dir DIR]

Builds each benchmarks/bend/<s>.bend and benchmarks/native/<s>.c and runs every
row of benchmarks/workloads.py for that structure with a small count (both
region orders), comparing the three checksums each side prints on stderr.
It only checks that the drivers still do the identical work; the gate does
the same comparison on its own runs.
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'benchmarks'))
import workloads  # noqa: E402

LOCK = json.loads((ROOT / 'inventory' / 'toolchain.json').read_text())
BEND = LOCK['binary']
CFLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
OUT = ROOT / 'build' / 'quick'


def sums(cmd):
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=600)
    return [l for l in r.stderr.splitlines() if l.strip()][:3], r.returncode


def main():
    names = [a for a in sys.argv[1:] if not a.startswith('--')]
    if not names:
        names = sorted({w['structure'] for w in workloads.TABLE})
    OUT.mkdir(parents=True, exist_ok=True)
    bad = 0
    for name in names:
        bbin = OUT / ('%s.cs.bin' % name)
        cbin = OUT / ('%s.cs.c.bin' % name)
        p = subprocess.run([BEND, 'benchmarks/bend/%s.bend' % name, '-o', str(bbin)], cwd=ROOT, capture_output=True, text=True)
        if p.returncode != 0 or not bbin.exists():
            print(name, 'BUILD FAILED', p.stdout[-500:], p.stderr[-500:])
            bad += 1
            continue
        subprocess.run(['cc'] + CFLAGS + ['-o', str(cbin), 'benchmarks/native/%s.c' % name], cwd=ROOT, check=True)
        rows = [w for w in workloads.TABLE if w['structure'] == name]
        ok = 0
        for w in rows:
            size = min(w['size'], 4096)
            count = max(1, min(w['count'], 50))
            args = [str(w['op']), str(size), str(count), '1', '4242']
            for order in ['0', '1']:
                b, rb = sums([str(bbin), '--threads', '1', '--'] + args + [order])
                c, rc = sums([str(cbin)] + args + [order])
                if order == '1':
                    b = list(reversed(b))  # Bend prints in run order (C, B, A); C always prints A, B, C
                if b != c or rb != 0 or rc != 0:
                    bad += 1
                    print('MISMATCH', name, w['operation'], w['workload'], order, b, c, rb, rc)
                    break
            else:
                ok += 1
        print('%-22s %d/%d rows match' % (name, ok, len(rows)), flush=True)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
