#!/usr/bin/env python3
"""Differential test: benchmarks/bend/lru.bend against benchmarks/native/lru.c.

Builds the Bend driver natively and the C reference twice (the benchmark
flags, and -fsanitize=address,undefined), runs every selector over a grid of
sizes, counts and seeds in both region orders, and requires all three region
checksums to agree bit for bit across the three binaries. Any sanitizer
report makes the run fail (ASan/UBSan abort on error).

    python3 tools/lru_diff.py [--quick]
"""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BEND = os.environ.get('BEND', str(Path.home() / '.bend' / 'bin' / 'bend'))
OUT = ROOT / 'build' / 'lru_diff'
CC = os.environ.get('CC', 'cc')
FLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
SAN = ['-O1', '-g', '-std=c11', '-fno-strict-aliasing', '-fno-omit-frame-pointer',
       '-fsanitize=address,undefined', '-fno-sanitize-recover=all']
ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1',
       'ASAN_OPTIONS': 'detect_leaks=0:abort_on_error=1',
       'UBSAN_OPTIONS': 'halt_on_error=1:print_stacktrace=1'}


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    src = ROOT / 'benchmarks' / 'native' / 'lru.c'
    for name, flags in (('c', FLAGS), ('csan', SAN)):
        subprocess.run([CC] + flags + ['-o', str(OUT / name), str(src)], check=True)
    p = subprocess.run([BEND, 'benchmarks/bend/lru.bend', '-o', str(OUT / 'bend')],
                       cwd=ROOT, capture_output=True, text=True)
    if not (OUT / 'bend').exists():
        raise SystemExit(p.stdout + p.stderr)


def sums(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, env=ENV, timeout=600)
    if p.returncode != 0:
        raise SystemExit('FAILED %s\n%s' % (' '.join(cmd), p.stderr[-2000:]))
    return [ln for ln in p.stderr.splitlines() if ln.strip().isdigit()]


def main():
    quick = '--quick' in sys.argv
    build()
    sizes = [0, 1, 2, 3, 7, 64, 257] if quick else [0, 1, 2, 3, 5, 8, 64, 100, 257, 1000, 4096]
    counts = [0, 1, 13, 200] if quick else [0, 1, 2, 13, 200, 1500]
    seeds = [1, 99991]
    ops = list(range(20))
    n = bad = 0
    for op in ops:
        # the pooled selectors 18/19 build 2 * count independent caches of
        # `size` entries per region, so their grid is bounded to keep the
        # differential test's memory sane (the operations themselves are the
        # same lru_purge / lru_resize the other selectors call)
        pooled = op in (18, 19)
        for size in ([0, 1, 2, 3, 7, 64] if pooled else sizes):
            for count in ([0, 1, 13, 40] if pooled else counts):
                for seed in seeds:
                    for order in (0, 1):
                        args = [str(op), str(size), str(count), '2', str(seed), str(order)]
                        b = sums([str(OUT / 'bend'), '--threads', '1', '--'] + args)
                        if order:
                            b = b[::-1]
                        c = sums([str(OUT / 'c')] + args)
                        s = sums([str(OUT / 'csan')] + args)
                        n += 1
                        if not (b == c == s):
                            bad += 1
                            print('MISMATCH op=%d size=%d count=%d seed=%d order=%d bend=%s c=%s san=%s'
                                  % (op, size, count, seed, order, b, c, s))
    print('%d cases, %d mismatches' % (n, bad))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
