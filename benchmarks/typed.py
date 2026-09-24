#!/usr/bin/env python3
"""The templated math per type (src/math/generic.bend with the U32, U64 and
F32 instances, and the software F64): Bend (native C backend, one thread)
against C with uint32_t, uint64_t, float and double.

  python3 benchmarks/typed.py --report build/bench/typed.json

Both sides are rebuilt: benchmarks/bend/typed.bend with Bend and
benchmarks/native/typed.c at -O3 -march=native. Each operation runs COUNT
calls on arguments from the same MINSTD stream; the checksum of all results
must agree between Bend and C. One warm-up and five samples per side in
alternating order; the median is reported, in ns per call. The `loop` row
is the generator and checksum alone, part of every other row.
"""
import argparse, json, os, shutil, statistics, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'bench' / 'typed'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11']
SAMPLES = 5
# calls per sample: ~200 ms of Bend time per row (IO.now counts milliseconds)
OPS = [('loop', 4000000), ('u32_gcd', 300000), ('u32_isqrt', 100000), ('u32_comb', 200000),
       ('u32_factorial', 500000), ('u32_pow_mod', 120000), ('u64_gcd', 25000), ('u64_isqrt', 12000),
       ('u64_comb', 35000), ('u64_factorial', 100000), ('u64_pow_mod', 7000), ('f32_pow', 2000000),
       ('f32_clamp', 2000000), ('f64_add', 250000), ('f64_mul', 170000), ('f64_div', 20000),
       ('f64_sqrt', 18000), ('f64_pow', 45000)]


def sh(cmd, env=None, timeout=3600):
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
    if p.returncode:
        raise SystemExit('failed: %s\n%s%s' % (' '.join(map(str, cmd)), p.stdout[-2000:], p.stderr[-2000:]))
    return p.stdout


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    sh([BEND, 'benchmarks/bend/typed.bend', '-o', str(OUT / 'bend_typed')])
    sh([CC] + CFLAGS + ['-o', str(OUT / 'c_typed'), 'benchmarks/native/typed.c', '-lm'])


def run(binary, env, bend):
    cmd = [str(OUT / binary)] + (['--threads', '1'] if bend else [])
    lines = sh(cmd, env={**os.environ, **env}).splitlines()
    return float(lines[0].split('=')[1]), lines[1]


def measure(op, count):
    env = {'TYPED_OP': op, 'TYPED_COUNT': str(count)}
    run('bend_typed', env, True), run('c_typed', env, False)
    t, sums = {'bend': [], 'c': []}, {}
    for i in range(SAMPLES):
        order = [('bend', 'bend_typed', True), ('c', 'c_typed', False)]
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
    print('%-14s bend %9.1f ns  C %8.2f ns  ratio %7.2f' % (op, ns['bend'], ns['c'], r['ratio'] or 0), flush=True)
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
