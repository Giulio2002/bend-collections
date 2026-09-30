#!/usr/bin/env python3
"""Differential test of the software binary64's rounding, conversion,
exponent, neighbour, remainder and ratio functions (src/math/f64.bend)
against CPython (math, struct; the machine's IEEE doubles).

Operands are random bit patterns of every class (zeros, subnormals, normals
near every exponent, integers and half-integers, huge/tiny, infinities, NaN)
plus the special values of the design reference's Appendix A, run through
build/math/f64x (tests/math/f64x.bend). A NaN result matches any NaN. Prints
a JSON verdict naming the spec/math/f64.bend clause of each case; exit
status 1 on a mismatch.
"""
import json, math, random, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/f64x'
BATCH = 300
M64 = (1 << 64) - 1
CLAUSE = {'trunc': 'Trunc.value', 'floor': 'Floor.value', 'ceil': 'Ceil.value', 'round': 'Round.value',
          'to_u64': 'ToU64.value', 'to_u32': 'ToU32.value', 'floor_u64': 'FloorU64.value',
          'ceil_u64': 'CeilU64.value', 'round_u64': 'RoundU64.value', 'of_u64': 'OfU64.value',
          'frexp': 'Frexp.value', 'ldexp': 'Ldexp.value', 'ulp': 'Ulp.value', 'nextafter': 'Nextafter.value',
          'fmin': 'Fmin.value', 'fmax': 'Fmax.value', 'isnormal': 'IsNormal.value',
          'issubnormal': 'IsSubnormal.value', 'is_integer': 'IsInteger.value', 'modf': 'Modf.value',
          'fmod': 'Fmod.value', 'remainder': 'Remainder.value', 'isclose': 'IsClose.value',
          'ratio': 'AsIntegerRatio.value', 'bits': 'Bits.roundtrip'}
OPS = list(CLAUSE)


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


def val(b):
    return struct.unpack('>d', struct.pack('>Q', b))[0]


def enc(b):
    return f'{b >> 32}_{b & 0xffffffff}'


def encf(x):
    return 'NaN' if math.isnan(x) else enc(bits(x))


def rnd_bits(rng):
    c = rng.random()
    s = rng.randrange(2) << 63
    if c < 0.05: return s | rng.choice([0, 0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001, 1, 0x7fefffffffffffff, 0x0010000000000000])
    if c < 0.12: return s | rng.randrange(1, 1 << 52)                                    # subnormal
    if c < 0.2: return s | (rng.choice([1, 2, 1022, 1023, 1074, 1075, 1076, 1086, 1087, 1088, 2045, 2046]) << 52) | rng.randrange(1 << 52)
    if c < 0.35: return bits(float(rng.randrange(-(1 << 20), 1 << 20)))                   # small integers
    if c < 0.45: return bits(rng.randrange(-(1 << 20), 1 << 20) + 0.5)                     # half-integers (ties)
    if c < 0.55: return bits(rng.randrange(-(1 << 60), 1 << 60) * 1.0)                     # large integers
    if c < 0.7: return s | (rng.randrange(1000, 1100) << 52) | rng.randrange(1 << 52)
    return rng.randrange(1 << 64)


def pair(rng):
    a = rnd_bits(rng)
    c = rng.random()
    if c < 0.2:                                                                          # close exponents
        e = (a >> 52) & 0x7ff
        e2 = min(2046, max(0, e + rng.randrange(-8, 9)))
        return a, (rng.randrange(2) << 63) | (e2 << 52) | rng.randrange(1 << 52)
    if c < 0.3:                                                                          # ties for remainder
        m = rng.randrange(1, 1 << 20)
        y = rng.choice([1.0, 2.0, 0.5, 3.0, 1e-300, 1e300])
        return bits((m + 0.5) * y if y < 1e200 else m * y), bits(y)
    if c < 0.4:
        return a, a ^ (rng.randrange(2) << 63)
    return a, rnd_bits(rng)


def err(e):
    return 'E:ovf' if e == 'ovf' else 'E:dom'


def to_u64(x, bound=64):
    if math.isnan(x): return err('dom')
    if math.isinf(x): return err('ovf')
    t = math.trunc(x)
    if t < 0 or t >= (1 << bound): return err('ovf')
    return t


def expect(op, a, b, c, d, neg, k):
    x, y = val(a), val(b)
    if op in ('trunc', 'floor', 'ceil', 'round'):
        if math.isnan(x): return 'NaN'
        if math.isinf(x): return enc(a)
        f = {'trunc': math.trunc, 'floor': math.floor, 'ceil': math.ceil, 'round': round}[op](x)
        r = math.copysign(float(f), x) if f == 0 else float(f)
        return encf(r)
    if op in ('to_u64', 'floor_u64', 'ceil_u64', 'round_u64'):
        if op != 'to_u64' and not (math.isnan(x) or math.isinf(x)):
            x = float({'floor_u64': math.floor, 'ceil_u64': math.ceil, 'round_u64': round}[op](x))
        t = to_u64(x)
        return t if isinstance(t, str) else enc(t)
    if op == 'to_u32':
        t = to_u64(x, 64)
        if not isinstance(t, str) and t >= (1 << 32): t = err('ovf')
        return t if isinstance(t, str) else str(t)
    if op == 'of_u64': return encf(float(a))
    if op == 'frexp':
        if math.isnan(x): return 'NaN|0|0'
        m, e = math.frexp(x)
        return f'{encf(m)}|{1 if e < 0 else 0}|{abs(e)}'
    if op == 'ldexp':
        if math.isnan(x): return 'NaN'
        e = -k if neg else k
        try:
            r = math.ldexp(x, max(-5000, min(5000, e)))
        except OverflowError:
            r = math.copysign(math.inf, x)
        return encf(r)
    if op == 'ulp': return encf(math.ulp(x))
    if op == 'nextafter': return encf(math.nextafter(x, y))
    if op in ('fmin', 'fmax'):
        if math.isnan(x) and math.isnan(y): return 'NaN'
        if math.isnan(x): return enc(b)
        if math.isnan(y): return enc(a)
        if x == 0 and y == 0:
            sx, sy = math.copysign(1, x) < 0, math.copysign(1, y) < 0
            neg0 = (sx or sy) if op == 'fmin' else (sx and sy)
            return encf(-0.0 if neg0 else 0.0)
        if op == 'fmin': return enc(a) if x < y else enc(b)
        return enc(a) if y < x else enc(b)
    if op == 'isnormal':
        e = (a >> 52) & 0x7ff
        return '1' if 0 < e < 2047 else '0'
    if op == 'issubnormal':
        return '1' if ((a >> 52) & 0x7ff) == 0 and (a & ((1 << 52) - 1)) else '0'
    if op == 'is_integer':
        return '1' if (not math.isinf(x) and not math.isnan(x) and x.is_integer()) else '0'
    if op == 'modf':
        if math.isnan(x): return 'NaN|NaN'
        f, i = math.modf(x)
        return f'{encf(f)}|{encf(i)}'
    if op in ('fmod', 'remainder'):
        if math.isnan(x) or math.isnan(y) or math.isinf(x) or y == 0: return 'NaN'
        return encf((math.fmod if op == 'fmod' else math.remainder)(x, y))
    if op == 'isclose':
        rel, at = val(c), val(d)
        try:
            return '1' if math.isclose(x, y, rel_tol=rel, abs_tol=at) else '0'
        except ValueError:
            return 'E:dom'
    if op == 'ratio':
        if math.isnan(x): return 'E:dom'
        if math.isinf(x): return 'E:ovf'
        n, dd = x.as_integer_ratio()
        if abs(n) >= (1 << 64): return 'E:ovf'
        return f'{1 if n < 0 else 0}|{enc(abs(n))}|{dd.bit_length() - 1}'
    if op == 'bits': return enc(a)
    raise SystemExit('op ' + op)


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


def same(e, g):
    es, gs = str(e).split('|'), g.split('|')
    return len(es) == len(gs) and all(x == y or (x == 'NaN' and is_nan(y)) for x, y in zip(es, gs))


APPENDIX = [('floor', math.inf), ('floor', math.nan), ('ulp', 0.0), ('ulp', math.inf), ('modf', math.inf),
            ('frexp', math.inf), ('fmod', 5.0, math.inf), ('remainder', 5.0, 2.0), ('remainder', 7.0, 2.0),
            ('round', 0.5), ('round', 1.5), ('round', 2.5), ('round', -0.5), ('ceil', -0.5), ('nextafter', 1.0, 2.0),
            ('nextafter', 0.0, -1.0), ('nextafter', 5e-324, 0.0), ('nextafter', -5e-324, 0.0),
            ('nextafter', 1.7976931348623157e308, math.inf), ('ldexp', 1.0, 2000), ('ldexp', 1.0, -1080),
            ('isclose', 1e-10, 0.0), ('modf', -2.0), ('modf', -2.5), ('fmod', -7.0, 3.0), ('remainder', 5.0, 3.0)]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    rng = random.Random(seed)
    cases = []
    def add(op, a, b=0, c=0, d=0, neg=0, k=0):
        tok = f'{op}:{enc(a)}:{enc(b)}:{enc(c)}:{enc(d)}' if op != 'ldexp' else f'{op}:{enc(a)}:{neg}:{k}'
        cases.append((tok, expect(op, a, b, c, d, bool(neg), k)))
    for ap in APPENDIX:
        op, x = ap[0], ap[1]
        if op == 'ldexp':
            add(op, bits(x), neg=int(ap[2] < 0), k=abs(ap[2]))
        elif op == 'isclose':
            add(op, bits(x), bits(ap[2]), bits(1e-9), bits(0.0))
        else:
            add(op, bits(x), bits(ap[2]) if len(ap) > 2 else 0)
    for op in OPS:
        for _ in range(per):
            a, b = pair(rng)
            if op == 'ldexp':
                k = rng.choice([0, 1, 52, 1074, 1100, 2100, rng.randrange(0, 60), rng.randrange(0, 2200)])
                add(op, a, neg=rng.randrange(2), k=k)
            elif op == 'isclose':
                rel = rng.choice([1e-9, 0.0, 1e-3, 0.5, -1e-9, math.nan, 1e-15])
                at = rng.choice([0.0, 1e-12, 1e-300, 1.0, -0.0, -1e-3])
                if rng.random() < 0.3:
                    b = bits(val(a) * (1 + rng.choice([1e-10, 1e-8, 1e-16, 0.0]))) if not math.isnan(val(a)) else b
                add(op, a, b, bits(rel), bits(at))
            elif op == 'of_u64':
                add(op, rng.choice([rng.randrange(1 << 64), rng.randrange(1 << 53), (1 << 64) - rng.randrange(1, 1 << 11), rng.randrange(1 << 20) << rng.randrange(0, 44)]))
            else:
                add(op, a, b)
    got = run([t for t, _ in cases])
    bad = [(CLAUSE[t.split(':')[0]], t, e, g) for (t, e), g in zip(cases, got) if not same(e, g)]
    print(json.dumps({'seed': seed, 'cases': len(cases), 'clauses': sorted(set(CLAUSE.values())), 'failures': len(bad), 'examples': bad[:12]}, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
