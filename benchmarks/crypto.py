#!/usr/bin/env python3
"""SHA-256, Keccak-256, BLAKE2s, BLAKE2b and BLAKE3: Bend (native C backend, one thread) against C.

  python3 benchmarks/crypto.py --report build/bench/crypto.json

Both sides are rebuilt: benchmarks/bend/{sha256,keccak256,blake2s,blake2b,blake3}.bend with Bend, and
benchmarks/native/*.c with the C compiler at -O3 -march=native: portable FIPS
180-4 SHA-256, XKCP's fully unrolled portable Keccak (benchmarks/native/xkcp/),
the official BLAKE2 reference and the official BLAKE3 C built software-only
(benchmarks/native/blake/). Inputs are prepared before the timed
region; each size runs one warm-up and five samples per side in alternating
order, and the median is reported. SHA-256 digests must be identical between
Bend, C and Python's hashlib; the other checksums between Bend and C.
"""
import argparse, hashlib, json, os, shutil, statistics, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'bench' / 'crypto'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11']
SAMPLES = 5
# BLAKE3 reference: the official C, software only (no SIMD backends)
PORTABLE3 = ['-DBLAKE3_NO_SSE2', '-DBLAKE3_NO_SSE41', '-DBLAKE3_NO_AVX2', '-DBLAKE3_NO_AVX512', '-DBLAKE3_USE_NEON=0']


def sh(cmd, env=None, timeout=3600):
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
    if p.returncode:
        raise SystemExit('failed: %s\n%s%s' % (' '.join(map(str, cmd)), p.stdout[-2000:], p.stderr[-2000:]))
    return p.stdout


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    for n in ['sha256', 'keccak256', 'blake2s', 'blake2b', 'blake3']:
        sh([BEND, 'benchmarks/bend/%s.bend' % n, '-o', str(OUT / ('bend_' + n))])
    B = 'benchmarks/native/blake/'
    sh([CC] + CFLAGS + ['-I' + B, '-o', str(OUT / 'c_blake2s'), 'benchmarks/native/blake2s.c', B + 'blake2s-ref.c'])
    sh([CC] + CFLAGS + ['-I' + B, '-o', str(OUT / 'c_blake2b'), 'benchmarks/native/blake2b.c', B + 'blake2b-ref.c'])
    sh([CC] + CFLAGS + ['-I' + B] + PORTABLE3 + ['-o', str(OUT / 'c_blake3'), 'benchmarks/native/blake3.c',
        B + 'blake3.c', B + 'blake3_dispatch.c', B + 'blake3_portable.c'])
    sh([CC] + CFLAGS + ['-o', str(OUT / 'c_sha256'), 'benchmarks/native/sha256.c'])
    sh([CC] + CFLAGS + ['-Ibenchmarks/native/xkcp', '-o', str(OUT / 'c_keccak256'),
        'benchmarks/native/keccak256.c', 'benchmarks/native/xkcp/KeccakP-1600-opt64.c'])


def run(binary, env, bend):
    cmd = [str(OUT / binary)] + (['--threads', '1'] if bend else [])
    lines = sh(cmd, env={**os.environ, **env}).splitlines()
    return float(lines[0].split('=')[1]), lines[1:]


def measure(pair, env, check):
    bend_bin, c_bin = pair
    run(bend_bin, env, True), run(c_bin, env, False)             # warm-up
    t = {'bend': [], 'c': []}
    for i in range(SAMPLES):
        order = [('bend', bend_bin, True), ('c', c_bin, False)]
        for name, b, isb in (order if i % 2 == 0 else order[::-1]):
            ms, out = run(b, env, isb)
            check(name, out)
            t[name].append(ms)
    return {k: statistics.median(v) for k, v in t.items()}, t


def sha_rows():
    rows = []
    for size in [64, 1024, 16384, 65536, 1048576]:
        total = 4 * 1024 * 1024
        count = total // size
        data = bytes(((i * 2654435761 + 42) >> 7) & 0xff for i in range(count * size))
        expected = [hashlib.sha256(data[i * size:(i + 1) * size]).hexdigest() for i in range(count)][::-1]
        with tempfile.NamedTemporaryFile(delete=False) as f:
            f.write(data)
        env = {'SHA_BENCH_INPUT': f.name, 'SHA_BENCH_SIZE': str(size)}

        def check(name, out):
            assert out == expected, 'SHA-256 %s digests differ at size %d' % (name, size)
        med, samples = measure(('bend_sha256', 'c_sha256'), env, check)
        os.unlink(f.name)
        rows.append(row('sha256', size, count, med, samples))
    return rows


def array_rows(algo, prefix):
    """the packed-array hashes: env <prefix>_SIZE/_DEPTH/_COUNT, a checksum that must agree"""
    rows = []
    for size in [0, 64, 1024, 16384, 65536, 1048576]:
        depth = max(0, (((size + 3) // 4) - 1).bit_length())
        count = max(64, min(524288, 64 * 1024 * 1024 // max(1, size))) // 4
        env = {prefix + '_SIZE': str(size), prefix + '_DEPTH': str(depth), prefix + '_COUNT': str(count)}
        sums = {}

        def check(name, out):
            sums.setdefault(name, out[0])
            assert out[0] == sums[name], '%s %s checksum changed' % (algo, name)
        med, samples = measure(('bend_' + algo, 'c_' + algo), env, check)
        assert sums['bend'] == sums['c'], '%s checksums differ at size %d: %s' % (algo, size, sums)
        rows.append(row(algo, size, count, med, samples))
    return rows


def row(algo, size, count, med, samples):
    us = {k: v * 1000 / count for k, v in med.items()}
    r = {'algorithm': algo, 'bytes': size, 'hashes': count, 'us_per_hash': us,
         'mb_per_s': {k: (size * count / 1e6) / (v / 1e3) if size and v else None for k, v in med.items()},
         'ratio': us['bend'] / us['c'] if us['c'] else None, 'samples_ms': samples, 'verified': True}
    print('%-9s %8d B  bend %10.2f us  C %10.2f us  ratio %6.2f' % (algo, size, us['bend'], us['c'], r['ratio'] or 0), flush=True)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', required=True)
    a = ap.parse_args()
    build()
    rows = sha_rows() + array_rows('keccak256', 'KECCAK') + array_rows('blake2s', 'BLAKE') + array_rows('blake2b', 'BLAKE') + array_rows('blake3', 'BLAKE')
    cc = subprocess.run([CC, '--version'], capture_output=True, text=True).stdout.splitlines()[0]
    bv = subprocess.run([BEND, '--version'], capture_output=True, text=True).stdout.strip()
    rep = {'bend': bv, 'cc': cc, 'cflags': CFLAGS, 'samples': SAMPLES, 'rows': rows}
    Path(a.report).parent.mkdir(parents=True, exist_ok=True)
    Path(a.report).write_text(json.dumps(rep, indent=2))


if __name__ == '__main__':
    sys.exit(main())
