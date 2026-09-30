#!/usr/bin/env python3
"""The newer crypto and random modules: Bend (native C backend, one thread)
against C, one group per run.

  python3 benchmarks/crypto_suite.py --group hash   --report build/bench/suite-hash.json
  python3 benchmarks/crypto_suite.py --group cipher --report build/bench/suite-cipher.json
  python3 benchmarks/crypto_suite.py --group pk     --report build/bench/suite-pk.json
  python3 benchmarks/crypto_suite.py --group random --report build/bench/suite-random.json

  --only NAME[,NAME...]   measure only these cases (for development)
  --samples N             samples per row (default 5)

Protocol (benchmarks/bend/suite.bend and benchmarks/native/suite.h implement
the same one): BENCH_INPUT names a file of COUNT * SIZE bytes that the driver
cuts into COUNT messages of BENCH_SIZE bytes before the timed region; the
timed region applies the operation to every message (BENCH_PARAM selects a
variant: a chunk size, an output length, a parameter set); then BENCH_MS and a
checksum are printed. The checksum folds every output byte, last message
first, as c = c * 31 + byte (mod 2^32). The random group has no input file:
BENCH_SIZE is the number of draws (or the list length).

Every row must give the same checksum from Bend and C; where Python has the
algorithm (hashlib, hmac, the `cryptography` package) its checksum must agree
too. Each row runs one warm-up and SAMPLES samples per side in alternating
order; the median is reported.
"""
import argparse, json, os, shutil, statistics, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
OUT = ROOT / 'build' / 'bench' / 'suite'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11']
SAMPLES = 5
M32 = 0xffffffff


def sh(cmd, env=None, timeout=3600):
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
    if p.returncode:
        raise SystemExit('failed: %s\n%s%s' % (' '.join(map(str, cmd)), p.stdout[-3000:], p.stderr[-3000:]))
    return p.stdout


# ---- the shared checksum and inputs -------------------------------------

def fold(c, bs):
    for b in bs:
        c = (c * 31 + b) & M32
    return c


def checksum(outputs):
    """outputs in message order; folded last message first, as the drivers do"""
    c = 0
    for o in reversed(outputs):
        c = fold(c, o)
    return c


def pattern(n, a, b):
    """the fixed keys, nonces and salts of the drivers: byte i = (a*i + b) mod 256"""
    return bytes((a * i + b) & 0xff for i in range(n))


def message_bytes(count, size):
    """the message stream of crypto.py's SHA-256 rows"""
    return bytes(((i * 2654435761 + 42) >> 7) & 0xff for i in range(count * size))


# ---- builds --------------------------------------------------------------

def c_build(name, sources, incs=(), defs=()):
    sh([CC] + CFLAGS + ['-Ibenchmarks/native'] + ['-I' + i for i in incs] + list(defs) +
       ['-o', str(OUT / ('c_' + name))] + list(sources))


def bend_build(name):
    sh([BEND, 'benchmarks/bend/suite_%s.bend' % name, '-o', str(OUT / ('bend_' + name))])


# ---- measurement ----------------------------------------------------------

def run(binary, env, bend):
    cmd = [str(OUT / binary)] + (['--threads', '1'] if bend else [])
    lines = sh(cmd, env={**os.environ, **env}).split()
    kv = dict(l.split('=', 1) for l in lines if '=' in l)
    return float(kv['BENCH_MS']), kv['SUM']


def measure(sides, env, samples):
    """sides: [(label, binary, is_bend)]; one warm-up, then samples rotating the order"""
    sums = {}
    for label, b, isb in sides:
        sums[label] = run(b, env, isb)[1]
    t = {label: [] for label, _, _ in sides}
    for i in range(samples):
        order = sides[i % len(sides):] + sides[:i % len(sides)]
        if i % 2:
            order = order[::-1]
        for label, b, isb in order:
            ms, s = run(b, env, isb)
            assert s == sums[label], '%s checksum changed between runs' % label
            t[label].append(ms)
    return {k: statistics.median(v) for k, v in t.items()}, t, sums


def human(n):
    return '%d B' % n if n < 1024 else '%d KiB' % (n // 1024) if n < 1048576 else '%d MiB' % (n // 1048576)


def bench_case(case, samples):
    rows = []
    for spec in case['rows']:
        size, param, count = spec['size'], spec.get('param', 0), spec['count']
        env = {'BENCH_SIZE': str(size), 'BENCH_PARAM': str(param), 'BENCH_COUNT': str(count), **spec.get('env', {})}
        tmp = None
        if case.get('input', True):
            data = message_bytes(count, size)
            with tempfile.NamedTemporaryFile(delete=False, dir=OUT) as f:
                f.write(data)
                tmp = f.name
            env['BENCH_INPUT'] = tmp
        try:
            sides = [('bend', 'bend_' + case['bend'], True), ('c', 'c_' + case['c'], False)]
            if case.get('c_alt'):
                sides.append(('c_alt', 'c_' + case['c_alt'], False))
            med, raw, sums = measure(sides, env, spec.get('samples', samples))
        finally:
            if tmp:
                os.unlink(tmp)
        agree = len(set(sums.values())) == 1
        expected = None
        if case.get('py') and agree:
            msgs = [data[i * size:(i + 1) * size] for i in range(count)] if case.get('input', True) else None
            expected = str(case['py'](msgs, spec))
            agree = expected == sums['bend']
        if not agree:
            raise SystemExit('%s %s: checksums differ: %s python=%s' % (case['name'], spec, sums, expected))
        us = {k: v * 1000 / count for k, v in med.items()}
        r = {'case': case['name'], 'label': spec.get('label') or human(size), 'size': size, 'param': param,
             'count': count, 'us_per_op': us, 'ratio': us['bend'] / us['c'] if us['c'] else None,
             'samples_ms': raw, 'checksum': sums['bend'], 'python_checked': expected is not None}
        if 'c_alt' in us:
            r['ratio_alt'] = us['bend'] / us['c_alt'] if us['c_alt'] else None
        print('%-22s %-16s bend %11.2f us  C %11.2f us  ratio %8.2f%s' % (
            case['name'], r['label'], us['bend'], us['c'], r['ratio'] or 0,
            '  (alt C %.2f us, ratio %.2f)' % (us['c_alt'], r['ratio_alt']) if 'c_alt' in us else ''), flush=True)
        rows.append(r)
    return rows


def groups():
    import suite_cases
    return suite_cases.GROUPS


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--group', required=True)
    ap.add_argument('--report', required=True)
    ap.add_argument('--only')
    ap.add_argument('--samples', type=int, default=SAMPLES)
    a = ap.parse_args()
    G = groups()
    cases = G[a.group]
    if a.only:
        keep = a.only.split(',')
        cases = [c for c in cases if c['name'] in keep]
    OUT.mkdir(parents=True, exist_ok=True)
    built = set()
    for c in cases:
        if c['bend'] not in built:
            bend_build(c['bend'])
            built.add(c['bend'])
        for key in ('c', 'c_alt'):
            n = c.get(key)
            if n and ('c:' + n) not in built:
                c_build(n, *c['c_build'][n])
                built.add('c:' + n)
    rows = []
    report = Path(a.report)
    report.parent.mkdir(parents=True, exist_ok=True)
    cc = subprocess.run([CC, '--version'], capture_output=True, text=True).stdout.splitlines()[0]
    bv = subprocess.run([BEND, '--version'], capture_output=True, text=True).stdout.strip()
    for c in cases:
        rows += bench_case(c, a.samples)
        report.write_text(json.dumps({'group': a.group, 'bend': bv, 'cc': cc, 'cflags': CFLAGS,
                                      'samples': a.samples, 'rows': rows}, indent=1))


if __name__ == '__main__':
    sys.exit(main())
