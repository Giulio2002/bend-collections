#!/usr/bin/env python3
"""Differential test of src/math/fixed.bend (U32/U64 fixed-width families,
bit counts, primality, bytes) and src/math/number.bend (Nat bit_count, egcd,
is_prime) against Python integers with Rust's u32/u64 semantics:

  checked_*      None on overflow, a zero divisor, or a shift >= the width
  wrapping_*     modulo 2^w (shift amounts modulo w)
  saturating_*   clamped to [0, 2^w - 1]
  overflowing_*  (wrapping value, overflowed)

Every case names the spec/math/fixed.bend or spec/math/number.bend clause it
exercises. Inputs run through build/math/fixed (tests/math/fixed.bend).

  python3 tools/check_fixed.py [seed] [cases-per-op]

Prints a JSON verdict; exit status 1 on any mismatch.
"""
import json, math, random, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/fixed'
BATCH = 300

FAMILY = {'add': lambda a, b: a + b, 'sub': lambda a, b: a - b, 'mul': lambda a, b: a * b}
CLAUSE = {
    'checked_add': 'CheckedAdd.value', 'checked_sub': 'CheckedSub.value', 'checked_mul': 'CheckedMul.value',
    'checked_div': 'CheckedDiv.value', 'checked_rem': 'CheckedRem.value', 'checked_pow': 'CheckedPow.value',
    'checked_shl': 'CheckedShl.value', 'checked_shr': 'CheckedShr.value',
    'wrapping_add': 'WrappingAdd.value', 'wrapping_sub': 'WrappingSub.value', 'wrapping_mul': 'WrappingMul.value',
    'wrapping_pow': 'WrappingPow.value', 'wrapping_shl': 'WrappingShl.value', 'wrapping_shr': 'WrappingShr.value',
    'saturating_add': 'SaturatingAdd.value', 'saturating_sub': 'SaturatingSub.value',
    'saturating_mul': 'SaturatingMul.value', 'saturating_pow': 'SaturatingPow.value',
    'overflowing_add': 'OverflowingAdd.value', 'overflowing_sub': 'OverflowingSub.value',
    'overflowing_mul': 'OverflowingMul.value', 'overflowing_pow': 'OverflowingPow.value',
    'overflowing_shl': 'OverflowingShl.value', 'overflowing_shr': 'OverflowingShr.value',
    'bit_count': 'BitCount.value', 'is_prime': 'IsPrime.value', 'next_prime': 'NextPrime.value',
    'to_bytes_le': 'ToBytes.le', 'to_bytes_be': 'ToBytes.be', 'from_bytes_le': 'FromBytes.le',
    'from_bytes_be': 'FromBytes.be', 'egcd': 'Egcd.bezout'}
BINARY = ['checked_add', 'checked_sub', 'checked_mul', 'checked_div', 'checked_rem', 'wrapping_add', 'wrapping_sub',
          'wrapping_mul', 'saturating_add', 'saturating_sub', 'saturating_mul', 'overflowing_add', 'overflowing_sub',
          'overflowing_mul']
EXPONENT = ['checked_pow', 'wrapping_pow', 'saturating_pow', 'overflowing_pow']
SHIFT = ['checked_shl', 'checked_shr', 'wrapping_shl', 'wrapping_shr', 'overflowing_shl', 'overflowing_shr']


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def show(v, w):
    return str(v) if w == 32 else '%d_%d' % (v >> 32, v & 0xFFFFFFFF)


def expect(op, w, a, b):
    lim = 1 << w
    fam = op.split('_', 1)[1] if '_' in op else op
    if op.startswith('checked_'):
        if fam in FAMILY:
            r = FAMILY[fam](a, b)
            return 'None' if r < 0 or r >= lim else show(r, w)
        if fam in ('div', 'rem'):
            return 'None' if b == 0 else show(a // b if fam == 'div' else a % b, w)
        if fam == 'pow':
            r = a ** b if a < 2 or b < 64 else lim
            return 'None' if r >= lim else show(r, w)
        if fam == 'shl':
            return 'None' if b >= w else show((a << b) % lim, w)
        if fam == 'shr':
            return 'None' if b >= w else show(a >> b, w)
    if op.startswith('wrapping_'):
        if fam in FAMILY:
            return show(FAMILY[fam](a, b) % lim, w)
        if fam == 'pow':
            return show(pow(a, b, lim), w)
        if fam == 'shl':
            return show((a << (b % w)) % lim, w)
        if fam == 'shr':
            return show(a >> (b % w), w)
    if op.startswith('saturating_'):
        if fam in FAMILY:
            return show(min(max(FAMILY[fam](a, b), 0), lim - 1), w)
        if fam == 'pow':
            r = a ** b if a < 2 or b < 64 else lim
            return show(min(r, lim - 1), w)
    if op.startswith('overflowing_'):
        if fam in FAMILY:
            r = FAMILY[fam](a, b)
            return '%s,%d' % (show(r % lim, w), int(r < 0 or r >= lim))
        if fam == 'pow':
            r = a ** b if a < 2 or b < 64 else lim
            return '%s,%d' % (show(pow(a, b, lim), w), int(r >= lim))
        if fam == 'shl':
            return '%s,%d' % (show((a << (b % w)) % lim, w), int(b >= w))
        if fam == 'shr':
            return '%s,%d' % (show(a >> (b % w), w), int(b >= w))
    raise ValueError(op)


def arg(w, rng):
    lim = 1 << w
    return rng.choice([0, 1, 2, 3, lim - 1, lim - 2, 1 << (w // 2), (1 << (w // 2)) - 1, (1 << (w // 2)) + 1,
                       rng.randrange(lim), rng.randrange(1 << (w // 2)), rng.randrange(1 << 8), rng.randrange(lim)])


def small_prime_case(w, rng):
    # near 2^32 (both types), where the trial division is the slowest
    return rng.choice([rng.randrange(1 << 20), rng.randrange(1 << 32), (1 << 32) - rng.randrange(1, 300),
                       rng.choice([2, 3, 4, 97, 65521, 65537, 4294967291, 4294967279])])


def cases(rng, per):
    out = []
    for w, ty in ((32, 'u32'), (64, 'u64')):
        for op in BINARY:
            for _ in range(per):
                a, b = arg(w, rng), arg(w, rng)
                out.append(('%s:%s:%s:%s' % (ty, op, show(a, w), show(b, w)), expect(op, w, a, b)))
        # 64-bit division by a two-limb divisor (b >= 2^32): the quotient
        # estimate and its correction loop near q = 2^32 - 1
        if w == 64:
            for _ in range(per):
                b = rng.choice([(1 << 32) + rng.randrange(1, 1 << 12), (1 << 32) + 1, rng.randrange(1 << 32, 1 << 40),
                                rng.randrange(1 << 32, 1 << 64)])
                a = rng.choice([(1 << 64) - rng.randrange(1, 1 << 20), rng.randrange(1 << 64),
                                b * rng.randrange(1, 1 << 32) - rng.randrange(0, 2)])
                a %= 1 << 64
                for op in ('checked_div', 'checked_rem'):
                    out.append(('u64:%s:%s:%s' % (op, show(a, w), show(b, w)), expect(op, w, a, b)))
        for op in EXPONENT:
            for _ in range(per):
                a = rng.choice([0, 1, 2, 3, 7, 10, 255, 65535, arg(w, rng)])
                e = rng.choice([0, 1, 2, 5, 16, 31, 32, 33, 63, 64, rng.randrange(1 << 32)])
                out.append(('%s:%s:%s:%d' % (ty, op, show(a, w), e), expect(op, w, a, e)))
        for op in SHIFT:
            for _ in range(per):
                a = arg(w, rng)
                s = rng.choice([0, 1, w - 1, w, w + 1, 2 * w, rng.randrange(w), rng.randrange(1 << 32)])
                out.append(('%s:%s:%s:%d' % (ty, op, show(a, w), s), expect(op, w, a, s)))
        for _ in range(per):
            a = arg(w, rng)
            out.append(('%s:bit_count:%s' % (ty, show(a, w)), str(bin(a).count('1'))))
            le = [(a >> (8 * i)) & 255 for i in range(w // 8)]
            out.append(('%s:to_bytes_le:%s' % (ty, show(a, w)), ','.join(map(str, le))))
            out.append(('%s:to_bytes_be:%s' % (ty, show(a, w)), ','.join(map(str, le[::-1]))))
            bs = [rng.randrange(256) for _ in range(w // 8)]
            if rng.random() < 0.2:
                bs[rng.randrange(len(bs))] = rng.choice([256, 300, 4294967295])
            if rng.random() < 0.1:
                bs = bs[:-1] if rng.random() < 0.5 else bs + [1]
            ok = len(bs) == w // 8 and all(b < 256 for b in bs)
            val = sum(b << (8 * i) for i, b in enumerate(bs)) if ok else None
            out.append(('%s:from_bytes_le:%s' % (ty, '.'.join(map(str, bs))), show(val, w) if ok else 'None'))
            valb = sum(b << (8 * i) for i, b in enumerate(bs[::-1])) if ok else None
            out.append(('%s:from_bytes_be:%s' % (ty, '.'.join(map(str, bs))), show(valb, w) if ok else 'None'))
    for _ in range(per):
        n = small_prime_case(32, rng)
        out.append(('u32:is_prime:%d' % n, '1' if is_prime(n) else '0'))
        n = rng.choice([rng.randrange(1 << 32), (1 << 32) - rng.randrange(1, 40), 0, 1, 2, 4294967290, 4294967291])
        m = n + 1
        while m < (1 << 32) and not is_prime(m):
            m += 1
        out.append(('u32:next_prime:%d' % n, str(m) if m < (1 << 32) else 'None'))
        k = rng.choice([0, 1, 2, rng.randrange(1 << 20), rng.randrange(1 << 40), (1 << 47) - 1])
        out.append(('nat:bit_count:%d' % k, str(bin(k).count('1'))))
        p = rng.choice([0, 1, 2, 9, 97, rng.randrange(1 << 24), rng.randrange(1 << 32)])
        out.append(('nat:is_prime:%d' % p, '1' if is_prime(p) else '0'))
        a, b = rng.choice([0, 1, rng.randrange(1 << 20), rng.randrange(1 << 40)]), rng.choice([0, 1, rng.randrange(1 << 20), rng.randrange(1 << 40)])
        out.append(('nat:egcd:%d:%d' % (a, b), ('egcd', a, b)))
    return out


# Deterministic edge values (word and limb boundaries); they run on every seed.
EDGE = [0, 1, 2, (1 << 16) - 1, 1 << 16, (1 << 16) + 1, 1 << 31, (1 << 32) - 1, 1 << 32, (1 << 32) + 1,
        (1 << 48) - 1, 1 << 48, 1 << 63, (1 << 64) - 2, (1 << 64) - 1]


def edge_cases():
    out = []
    for w, ty in ((32, 'u32'), (64, 'u64')):
        e = [v for v in EDGE if v < (1 << w)]
        for op in BINARY:
            for a in e:
                for b in e:
                    out.append(('%s:%s:%s:%s' % (ty, op, show(a, w), show(b, w)), expect(op, w, a, b)))
        for op in EXPONENT:
            for a in e:
                for k in (0, 1, 2, 31, 32, 33, 63, 64, 65, (1 << 32) - 1):
                    out.append(('%s:%s:%s:%d' % (ty, op, show(a, w), k), expect(op, w, a, k)))
        for op in SHIFT:
            for a in e:
                for k in (0, 1, w - 1, w, w + 1, 2 * w, (1 << 32) - 1):
                    out.append(('%s:%s:%s:%d' % (ty, op, show(a, w), k), expect(op, w, a, k)))
        for a in e:
            out.append(('%s:bit_count:%s' % (ty, show(a, w)), str(bin(a).count('1'))))
            le = [(a >> (8 * i)) & 255 for i in range(w // 8)]
            out.append(('%s:to_bytes_le:%s' % (ty, show(a, w)), ','.join(map(str, le))))
            out.append(('%s:to_bytes_be:%s' % (ty, show(a, w)), ','.join(map(str, le[::-1]))))
            out.append(('%s:from_bytes_le:%s' % (ty, '.'.join(map(str, le))), show(a, w)))
            out.append(('%s:from_bytes_be:%s' % (ty, '.'.join(map(str, le[::-1]))), show(a, w)))
    for n in [v for v in EDGE if v < (1 << 32)] + [4294967291, 4294967290, 4294967292]:
        out.append(('u32:is_prime:%d' % n, '1' if is_prime(n) else '0'))
        m = n + 1
        while m < (1 << 32) and not is_prime(m):
            m += 1
        out.append(('u32:next_prime:%d' % n, str(m) if m < (1 << 32) else 'None'))
    for k in [v for v in EDGE if v < (1 << 48)] + [(1 << 47) - 1]:
        out.append(('nat:bit_count:%d' % k, str(bin(k).count('1'))))
    return out


def egcd_ok(got, a, b):
    try:
        g, x, y, neg = got.split(',')
        g, x, y = int(g), int(x), int(y)
    except ValueError:
        return False
    if g != math.gcd(a, b):
        return False
    return (b * y == g + a * x) if neg == '1' else (a * x == g + b * y)


def run(tokens):
    out = []
    for i in range(0, len(tokens), BATCH):
        chunk = tokens[i:i + BATCH]
        p = subprocess.run([str(BIN), '--threads', '1', '--'] + chunk, capture_output=True, text=True, timeout=1800)
        lines = p.stdout.strip().split('\n') if p.stdout.strip() else []
        if p.returncode != 0 or len(lines) != len(chunk):
            # a crash or a short answer is a failure, never a pass
            print(f'driver exited {p.returncode} and printed {len(lines)} lines for {len(chunk)} tokens: {p.stderr[-400:]}', file=sys.stderr)
            sys.exit(2)
        out += lines
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    cs = cases(rng, per) + edge_cases()
    got = run([t for t, _ in cs])
    bad, covered = [], {}
    for (t, e), g in zip(cs, got):
        ty, op = t.split(':')[:2]
        name = ty.upper() + ' ' + CLAUSE[op]
        covered[name] = covered.get(name, 0) + 1
        ok = egcd_ok(g, e[1], e[2]) if isinstance(e, tuple) else g == e
        if not ok:
            bad.append((name, t, e if not isinstance(e, tuple) else 'bezout', g))
    print(json.dumps({'seed': seed, 'cases': len(cs), 'clauses': len(covered), 'failures': len(bad),
                      'examples': bad[:12]}, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
