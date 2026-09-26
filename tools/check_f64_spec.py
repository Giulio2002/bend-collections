#!/usr/bin/env python3
"""Validate the binary64 specification itself: a line-by-line Python mirror
of spec/math/f64.bend (same names, same Nat arithmetic) compared with the
machine's IEEE 754 doubles on random bit patterns, zeros, subnormals,
infinities, NaNs and rounding ties.

spec/math/f64.bend states src/math/f64.bend's contract (Add.value,
Sub.value, Mul.value, Div.value, Sqrt.value, Lt/Le/Eq.value, Neg/Abs/
Copysign.value, the classification clauses, OfNat.value); tools/check_f64.py
tests the implementation against the machine's doubles, and this script
tests the specification against them, so a slip in either shows up.

Usage: check_f64_spec.py [seed] [count]. Prints a JSON verdict; exit 1 on a
mismatch.
"""
import json, math, random, struct, sys


def p2(k): return 1 << k
def b2n(b): return 1 if b else 0
def pick(c, a, b): return a if c else b
def shift(k, x): return x << k                 # C.shift
def low(k, n): return n & (p2(k) - 1)          # C.low
def high(k, n): return n >> k                  # C.high
def fits(k, n): return n < p2(k)               # C.fits


# ---- the encoding (a double is its 64-bit pattern) ----

def hi_nat(x): return x >> 32
def lo_nat(x): return x & (p2(32) - 1)
def sign(x): return not fits(31, hi_nat(x))
def efield(x): return low(11, high(20, hi_nat(x)))
def frac(x): return lo_nat(x) + shift(32, low(20, hi_nat(x)))
def encode(s, ef, f):
    return ((high(32, f) + shift(20, ef + shift(11, b2n(s)))) % p2(32)) << 32 | (low(32, f) % p2(32))
def qnan(): return 0x7FF8000000000000
def inf(s): return pick(s, 0xFFF0000000000000, 0x7FF0000000000000)
def zero(s): return pick(s, 0x8000000000000000, 0)
def is_nan(x): return efield(x) == 2047 and frac(x) != 0
def is_inf(x): return efield(x) == 2047 and frac(x) == 0
def is_zero(x): return efield(x) == 0 and frac(x) == 0


# ---- the exact value m * 2^(xe - Z) ----

def zb(): return 3000
def mant(x): return frac(x) + shift(52, b2n(not efield(x) == 0))
def xexp(x): return pick(efield(x) == 0, zb() - 1074, efield(x) + zb() - 1075)
def nsub(a, b): return max(a - b, 0)          # Nat.sub saturates
def bit_length(n): return n.bit_length()       # M.bit_length (proved)
def isqrt(n): return math.isqrt(n)             # M.isqrt (proved)


# ---- rounding ----

def rne_up(q, r, h): return q + b2n(h < r or (r == h and q % 2 == 1))

def rne(m, k):
    if k == 0: return m
    return rne_up(high(k, m), low(k, m), shift(k - 1, 1))

def pack_e(s, ef, f): return pick(2047 <= ef, inf(s), encode(s, ef, f))
def pack_n(s, q, u): return pick(fits(52, q), encode(s, 0, q), pack_e(s, nsub(u + 1075, zb()), low(52, q)))
def pack(s, q, u): return pick(fits(53, q), pack_n(s, q, u), pack_e(s, nsub(1 + u + 1075, zb()), 0))

def round_u(s, m, x, u):
    return pack(s, rne(m, nsub(u, x)) if x <= u else shift(nsub(x, u), m), u)

def round_(s, m, x):
    if m == 0: return zero(s)
    return round_u(s, m, x, max(nsub(x + bit_length(m), 53), nsub(zb(), 1074)))


# ---- operations ----

def sub_mag(sa, a, sb, b, x):
    if a > b: return round_(sa, a - b, x)
    if a < b: return round_(sb, b - a, x)
    return zero(False)

def add_mag(sa, a, sb, b, x):
    return round_(sa, a + b, x) if sa == sb else sub_mag(sa, a, sb, b, x)

def add_fin(x, y):
    c = min(xexp(x), xexp(y))
    return add_mag(sign(x), shift(xexp(x) - c, mant(x)), sign(y), shift(xexp(y) - c, mant(y)), c)

def add_inf(x, y):
    if is_inf(x): return pick(is_inf(y) and sign(x) != sign(y), qnan(), x)
    return y if is_inf(y) else add_fin(x, y)

def add(x, y): return qnan() if is_nan(x) or is_nan(y) else add_inf(x, y)
def neg(x): return encode(not sign(x), efield(x), frac(x))

def mul_inf(x, y, s):
    if is_inf(x) or is_inf(y): return pick(is_zero(x) or is_zero(y), qnan(), inf(s))
    return round_(s, mant(x) * mant(y), nsub(xexp(x) + xexp(y), zb()))

def mul(x, y): return qnan() if is_nan(x) or is_nan(y) else mul_inf(x, y, sign(x) != sign(y))

def kq(): return 200

def div_fin(x, y, s):
    n = shift(kq(), mant(x))
    return round_(s, 2 * (n // mant(y)) + min(n % mant(y), 1), nsub(xexp(x) + zb(), xexp(y) + kq() + 1))

def div_cls(x, y, s):
    if is_inf(x): return pick(is_inf(y), qnan(), inf(s))
    if is_inf(y): return zero(s)
    if is_zero(y): return pick(is_zero(x), qnan(), inf(s))
    return div_fin(x, y, s)

def div(x, y): return qnan() if is_nan(x) or is_nan(y) else div_cls(x, y, sign(x) != sign(y))

def kr(): return 100

def sqrt_even(m, x):
    n = shift(2 * kr(), m)
    r = isqrt(n)
    return round_(False, 2 * r + b2n(r * r != n), nsub(x // 2 + zb() // 2, kr() + 1))

def sqrt_fin(x):
    return sqrt_even(mant(x), xexp(x)) if xexp(x) % 2 == 0 else sqrt_even(2 * mant(x), xexp(x) - 1)

def sqrt_cls(x):
    if is_zero(x): return x
    if sign(x): return qnan()
    return x if is_inf(x) else sqrt_fin(x)

def sqrt(x): return qnan() if is_nan(x) else sqrt_cls(x)


# ---- comparisons ----

def cmp(a, b): return (a > b) - (a < b)

def mag_cmp(x, y):
    if is_inf(x): return pick(is_inf(y), 0, 1)
    if is_inf(y): return -1
    c = min(xexp(x), xexp(y))
    return cmp(shift(xexp(x) - c, mant(x)), shift(xexp(y) - c, mant(y)))

def ord_(x, y):
    if is_zero(x) and is_zero(y): return 0
    if sign(x) == sign(y): return -mag_cmp(x, y) if sign(x) else mag_cmp(x, y)
    return -1 if sign(x) else 1

def ordered(x, y): return not (is_nan(x) or is_nan(y))


# ---- the machine's doubles ----

def bits(d): return struct.unpack('>Q', struct.pack('>d', d))[0]
def dbl(b): return struct.unpack('>d', struct.pack('>Q', b))[0]
def canon(b): return qnan() if is_nan(b) else b


def machine(op, x, y):
    a, b = dbl(x), dbl(y)
    if op == 'add': return canon(bits(a + b))
    if op == 'sub': return canon(bits(a - b))
    if op == 'mul': return canon(bits(a * b))
    if op == 'div':
        if b == 0.0:
            if a == 0.0 or math.isnan(a): return qnan()
            return inf(sign(x) != sign(y))
        return canon(bits(a / b))
    if op == 'sqrt':
        if math.isnan(a) or (a < 0.0): return qnan()
        return bits(math.sqrt(a))
    if op == 'lt': return a < b
    if op == 'le': return a <= b
    if op == 'eq': return a == b
    raise ValueError(op)


def spec(op, x, y):
    if op == 'add': return add(x, y)
    if op == 'sub': return add(x, neg(y))
    if op == 'mul': return mul(x, y)
    if op == 'div': return div(x, y)
    if op == 'sqrt': return sqrt(x)
    if op == 'lt': return ordered(x, y) and ord_(x, y) < 0
    if op == 'le': return ordered(x, y) and ord_(x, y) <= 0
    if op == 'eq': return ordered(x, y) and ord_(x, y) == 0
    raise ValueError(op)


CLAUSE = {'add': 'Add.value', 'sub': 'Sub.value', 'mul': 'Mul.value', 'div': 'Div.value',
          'sqrt': 'Sqrt.value', 'lt': 'Lt.value', 'le': 'Le.value', 'eq': 'Eq.value'}


def rnd(rng):
    c = rng.random()
    if c < 0.08: return bits(rng.choice([0.0, -0.0, math.inf, -math.inf, math.nan, 1.0, -1.0, 5e-324, -5e-324, 2.2250738585072014e-308, 1.7976931348623157e308]))
    if c < 0.2: return (rng.getrandbits(1) << 63) | rng.getrandbits(52)            # subnormal
    if c < 0.3: return (rng.getrandbits(1) << 63) | (rng.choice([1, 2, 2045, 2046]) << 52) | rng.getrandbits(52)
    if c < 0.45: return bits(float(rng.randrange(-10 ** 6, 10 ** 6)))
    return rng.getrandbits(64)


def tie_pairs(rng):
    # sums landing exactly halfway between two doubles
    a = float(rng.randrange(1, 2 ** 52) * 2 + 1) * 2.0 ** rng.randrange(-60, 60)
    b = math.ldexp(1.0, math.frexp(a)[1] - 54)
    return bits(a), bits(b)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    rng = random.Random(seed)
    bad, n = [], 0
    for i in range(count):
        x, y = (tie_pairs(rng) if i % 10 == 0 else (rnd(rng), rnd(rng)))
        for op in CLAUSE:
            got, want = spec(op, x, y), machine(op, x, y)
            n += 1
            if got != want:
                bad.append({'clause': CLAUSE[op], 'x': hex(x), 'y': hex(y), 'spec': str(got), 'machine': str(want)})
        for (clause, got, want) in [('Neg.value', neg(x), bits(-dbl(x)) if not is_nan(x) else neg(x)),
                                    ('Abs.value', encode(False, efield(x), frac(x)), bits(abs(dbl(x))) if not is_nan(x) else encode(False, efield(x), frac(x))),
                                    ('IsNan.value', is_nan(x), math.isnan(dbl(x))),
                                    ('IsInf.value', is_inf(x), math.isinf(dbl(x))),
                                    ('IsZero.value', is_zero(x), dbl(x) == 0.0),
                                    ('Signbit.value', sign(x), math.copysign(1.0, dbl(x)) < 0)]:
            n += 1
            if got != want: bad.append({'clause': clause, 'x': hex(x), 'spec': str(got), 'machine': str(want)})
        k = rng.randrange(0, 2 ** rng.choice([8, 30, 48, 53, 60]))
        n += 1
        if round_(False, k, zb()) != bits(float(k)):
            bad.append({'clause': 'OfNat.value', 'n': k})
    print(json.dumps({'seed': seed, 'checked': n, 'failures': len(bad), 'first': bad[:5]}, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
