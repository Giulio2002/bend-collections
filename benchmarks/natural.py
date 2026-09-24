#!/usr/bin/env python3
"""src/math/natural.bend: Bend (native C backend, one thread) against C.

  python3 benchmarks/natural.py --report build/bench/math.json

Both sides are rebuilt: benchmarks/bend/math.bend with Bend and
benchmarks/native/math.c at -O3 -march=native. Each operation runs COUNT
calls on arguments from the same MINSTD stream; the checksum of all results
must agree between Bend and C. One warm-up and five samples per side in
alternating order; the median is reported, in ns per call. The `loop` row
is the generator and checksum alone, part of every other row.
"""
import argparse, json, os, shutil, statistics, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'bench' / 'math'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11']
SAMPLES = 5
# calls per sample: ~200 ms of Bend time per row (IO.now counts milliseconds)
OPS = [('loop', 40000000), ('gcd', 4000000), ('lcm', 6000000), ('isqrt', 10000000), ('iroot3', 4000000),
       ('ilog10', 40000000), ('bit_length', 20000000), ('factorial', 20000000), ('perm', 20000000),
       ('comb', 10000000), ('pow_mod', 4000000), ('mod_inverse', 3000000), ('divmod', 40000000)]


def sh(cmd, env=None, timeout=3600):
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
    if p.returncode:
        raise SystemExit('failed: %s\n%s%s' % (' '.join(map(str, cmd)), p.stdout[-2000:], p.stderr[-2000:]))
    return p.stdout


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    sh([BEND, 'benchmarks/bend/math.bend', '-o', str(OUT / 'bend_math')])
    sh([CC] + CFLAGS + ['-o', str(OUT / 'c_math'), 'benchmarks/native/math.c', '-lm'])


def run(binary, env, bend):
    cmd = [str(OUT / binary)] + (['--threads', '1'] if bend else [])
    lines = sh(cmd, env={**os.environ, **env}).splitlines()
    return float(lines[0].split('=')[1]), lines[1]


def measure(op, count):
    env = {'MATH_OP': op, 'MATH_COUNT': str(count)}
    run('bend_math', env, True), run('c_math', env, False)
    t, sums = {'bend': [], 'c': []}, {}
    for i in range(SAMPLES):
        order = [('bend', 'bend_math', True), ('c', 'c_math', False)]
        for name, b, isb in (order if i % 2 == 0 else order[::-1]):
            ms, out = run(b, env, isb)
            sums.setdefault(name, out)
            assert out == sums[name], '%s %s checksum changed' % (op, name)
            t[name].append(ms)
    assert sums['bend'] == sums['c'], '%s checksums differ: %s' % (op, sums)
    med = {k: statistics.median(v) for k, v in t.items()}
    ns = {k: v * 1e6 / count for k, v in med.items()}
    r = {'operation': op, 'calls': count, 'ns_per_call': ns, 'ratio': ns['bend'] / ns['c'] if ns['c'] else None,
         'samples_ms': t, 'checksum': sums['c'], 'verified': True}
    print('%-12s bend %9.1f ns  C %8.2f ns  ratio %7.2f' % (op, ns['bend'], ns['c'], r['ratio'] or 0), flush=True)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', required=True)
    ap.add_argument('--only', default=None)
    a = ap.parse_args()
    build()
    rows = [measure(op, n) for op, n in OPS if not a.only or op in a.only.split(',')]
    cc = subprocess.run([CC, '--version'], capture_output=True, text=True).stdout.splitlines()[0]
    bv = subprocess.run([BEND, '--version'], capture_output=True, text=True).stdout.strip()
    rep = {'bend': bv, 'cc': cc, 'cflags': CFLAGS, 'samples': SAMPLES, 'rows': rows}
    Path(a.report).parent.mkdir(parents=True, exist_ok=True)
    Path(a.report).write_text(json.dumps(rep, indent=2))


if __name__ == '__main__':
    sys.exit(main())
