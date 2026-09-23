#!/usr/bin/env python3
"""Differential test of the LRU (src/containers/lru.bend) against its
specification (proofs/spec/lru.bend): tests/lru_spec/main.bend runs both on
pseudo-random operation sequences (add, get, peek, contains, remove, keys,
resize, set_lifetime, purge, with a moving clock) and compares every result,
the length and all five counters after each step.

    python3 tools/check_lru_spec.py [--seeds N] [--ops N]
"""
import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
from toolchain import BEND, ENV  # noqa: E402

BIN = ROOT / 'build' / 'lru_spec_test'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seeds', type=int, default=24)
    ap.add_argument('--ops', type=int, default=4000)
    a = ap.parse_args()
    BIN.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([BEND, 'tests/lru_spec/main.bend', '-o', str(BIN)],
                       cwd=ROOT, capture_output=True, text=True, env=ENV)
    if p.returncode != 0 or not BIN.exists():
        print('build failed: ' + (p.stdout + p.stderr)[-400:])
        return 1
    for seed in range(1, a.seeds + 1):
        r = subprocess.run([str(BIN), str(seed), str(a.ops)], capture_output=True, text=True, env=ENV)
        out = r.stdout.strip()
        if r.returncode != 0 or out != 'OK %d' % a.ops:
            print('seed %d: %s' % (seed, out or r.stderr[-300:]))
            return 1
    print('lru matches its specification: %d seeds x %d ops' % (a.seeds, a.ops))
    return 0


if __name__ == '__main__':
    sys.exit(main())
