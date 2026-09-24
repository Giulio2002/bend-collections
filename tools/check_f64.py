#!/usr/bin/env python3
"""Differential test of the software binary64 (src/math/f64.bend) against the
machine's IEEE doubles (CPython floats; math.sqrt is correctly rounded).

Operands are random bit patterns from every class (zeros, subnormals, normals
near every exponent, huge/tiny, infinities, NaN) plus cancellation and
halfway-case pairs, run through build/math/f64 (tests/math/f64.bend). A NaN
result matches any NaN. Prints a JSON verdict; exit status 1 on a mismatch.
"""
import json, math, random, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/f64'
BATCH = 400
OPS = ['add', 'sub', 'mul', 'div', 'sqrt', 'lt', 'le', 'eq', 'neg', 'abs', 'copysign', 'of_nat']


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


def val(b):
    return struct.unpack('>d', struct.pack('>Q', b))[0]


def enc(b):
    return f'{b >> 32}_{b & 0xffffffff}'


def rnd_bits(rng):
    c = rng.random()
    s = rng.randrange(2) << 63
    if c < 0.05: return s | rng.choice([0, 0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001, 1])
    if c < 0.15: return s | rng.randrange(1, 1 << 52)                       # subnormal
    if c < 0.25: return s | (rng.choice([1, 2, 3, 2045, 2046]) << 52) | rng.randrange(1 << 52)
    if c < 0.35: return bits(float(rng.randrange(-(1 << 20), 1 << 20)))       # small integers
    if c < 0.5: return s | (rng.randrange(1000, 1048) << 52) | rng.randrange(1 << 52)
    return rng.randrange(1 << 64)


def pair(rng):
    a = rnd_bits(rng)
    c = rng.random()
    if c < 0.15:                                     # near-cancellation
        return a, (a ^ (1 << 63)) + rng.randrange(-3, 4) & ((1 << 64) - 1)
    if c < 0.25:                                     # close exponents
        e = (a >> 52) & 0x7ff
        e2 = min(2046, max(0, e + rng.randrange(-60, 61)))
        return a, (rng.randrange(2) << 63) | (e2 << 52) | rng.randrange(1 << 52)
    return a, rnd_bits(rng)


def expect(op, a, b, n):
    x, y = val(a), val(b)
    try:
        if op == 'add': r = x + y
        elif op == 'sub': r = x - y
        elif op == 'mul': r = x * y
        elif op == 'div':
            if y == 0.0:
                r = math.nan if (x == 0.0 or math.isnan(x)) else math.copysign(math.inf, x) * math.copysign(1.0, y)
            else: r = x / y
        elif op == 'sqrt':
            r = math.nan if (x < 0 or math.isnan(x)) else math.sqrt(x)
        elif op == 'lt': return '1' if x < y else '0'
        elif op == 'le': return '1' if x <= y else '0'
        elif op == 'eq': return '1' if x == y else '0'
        elif op == 'neg': return enc(a ^ (1 << 63))
        elif op == 'abs': return enc(a & ~(1 << 63))
        elif op == 'copysign': return enc((a & ~(1 << 63)) | (b & (1 << 63)))
        elif op == 'of_nat': r = float(n)
    except OverflowError:
        r = math.copysign(math.inf, x)
    return 'NaN' if math.isnan(r) else enc(bits(r))


def run(tokens):
    out = []
    for i in range(0, len(tokens), BATCH):
        chunk = tokens[i:i + BATCH]
        p = subprocess.run([str(BIN), '--threads', '1', '--'] + chunk, capture_output=True, text=True, timeout=1800)
        lines = p.stdout.strip().split('\n') if p.stdout.strip() else []
        if len(lines) != len(chunk):
            raise SystemExit(f'driver printed {len(lines)} lines for {len(chunk)} tokens: {p.stderr[-400:]}')
        out += lines
    return out


def is_nan(s):
    if '_' not in s: return False
    h, l = map(int, s.split('_'))
    return ((h >> 20) & 0x7ff) == 0x7ff and ((h & 0xfffff) or l)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    rng = random.Random(seed)
    cases = []
    for op in OPS:
        for _ in range(per):
            a, b = pair(rng)
            n = rng.choice([0, 1, rng.randrange(1 << 16), rng.randrange(1 << 47)])
            tok = f'of_nat:{n}' if op == 'of_nat' else f'{op}:{enc(a)}:{enc(b)}'
            cases.append((tok, expect(op, a, b, n)))
    got = run([t for t, _ in cases])
    bad = [(t, e, g) for (t, e), g in zip(cases, got) if not (e == g or (e == 'NaN' and is_nan(g)))]
    print(json.dumps({'seed': seed, 'cases': len(cases), 'failures': len(bad), 'examples': bad[:12]}, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
