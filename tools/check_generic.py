#!/usr/bin/env python3
"""Differential test of the templated math (src/math/generic.bend) for every
instance: U32 and U64 (checked: a result or intermediate that does not fit is
"Overflow"), F32 (numpy float32, rounded at every operation as the template
does) and the software F64 (Python floats; tools/check_f64.py covers its
arithmetic).

Inputs run through build/math/generic (tests/math/generic.bend). Prints a JSON
verdict; exit status 1 on any mismatch.
"""
import json, math, random, struct, subprocess, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/generic'
BATCH = 300
INT_OPS = ['gcd', 'lcm', 'isqrt', 'iroot', 'ilog', 'factorial', 'perm', 'comb', 'pow_mod', 'mod_inverse',
           'divmod', 'bit_length', 'clamp', 'gcd_all', 'lcm_all', 'prod', 'sum', 'min', 'max', 'abs', 'sign', 'pow']
F_OPS = ['clamp', 'prod', 'sum', 'min', 'max', 'abs', 'sign', 'pow']


def iroot(n, k):
    lo, hi = 0, 1 << (n.bit_length() // k + 1)
    while lo + 1 < hi:
        m = (lo + hi) // 2
        if m ** k <= n: lo = m
        else: hi = m
    return lo


def ilog(n, b):
    k, p = 0, 1
    while p * b <= n:
        p, k = p * b, k + 1
    return k


def checked(v, lim):
    return 'Overflow' if v >= lim else v


def int_expect(op, a, w):
    lim = 1 << w
    fit = lambda v: 'Overflow' if v >= lim else v
    if op == 'gcd': return math.gcd(a[0], a[1])
    if op == 'lcm': return fit(math.lcm(a[0], a[1]))
    if op == 'isqrt': return math.isqrt(a[0])
    if op == 'iroot': return 'Domain' if a[1] == 0 else iroot(a[0], a[1])
    if op == 'ilog': return 'Domain' if a[0] == 0 or a[1] < 2 else ('N', ilog(a[0], a[1]))
    if op == 'factorial':
        r = 1
        for i in range(2, a[0] + 1):
            r *= i
            if r >= lim: return 'Overflow'
        return r
    if op == 'perm':
        n, k = a
        if k > n: return 0
        r = 1
        for i in range(k):
            r *= n - i
            if r >= lim: return 'Overflow'
        return r
    if op == 'comb':
        n, k = a
        if k > n: return 0
        j, r = min(k, n - k), 1
        for i in range(j):
            r = r * (n - i) // (i + 1)
            if r >= lim: return 'Overflow'
        return r
    if op == 'pow_mod': return 'ZeroDivision' if a[2] == 0 else pow(a[0], a[1], a[2])
    if op == 'mod_inverse':
        if a[1] == 0: return 'ZeroDivision'
        try: return pow(a[0], -1, a[1])
        except ValueError: return 'NotInvertible'
    if op == 'divmod': return 'ZeroDivision' if a[1] == 0 else ('QR', a[0] // a[1], a[0] % a[1])
    if op == 'bit_length': return ('N', a[0].bit_length())
    if op == 'clamp': return 'Domain' if a[2] < a[1] else min(max(a[0], a[1]), a[2])
    if op == 'gcd_all':
        g = 0
        for x in a: g = math.gcd(g, x)
        return g
    if op == 'lcm_all':
        l = 1
        for x in a:
            l = math.lcm(l, x)
            if l >= lim: return 'Overflow'
        return l
    if op in ('prod', 'sum'):
        r = 1 if op == 'prod' else 0
        for x in a:
            r = r * x if op == 'prod' else r + x
            if r >= lim: return 'Overflow'
        return r
    if op == 'min': return a[1] if a[1] < a[0] else a[0]
    if op == 'max': return a[1] if a[0] < a[1] else a[0]
    if op == 'abs': return a[0]
    if op == 'sign': return 1 if a[0] > 0 else a[0]
    if op == 'pow': return fit(a[0] ** a[1]) if a[0] > 1 else a[0] ** a[1]
    raise ValueError(op)


def rnd_int(rng, w):
    c = rng.random()
    if c < 0.3: return rng.randrange(0, 64)
    if c < 0.55: return rng.randrange(0, 1 << 16)
    if c < 0.8: return rng.randrange(0, 1 << w)
    if c < 0.9: return (1 << w) - 1 - rng.randrange(0, 4)
    return rng.randrange(0, 1 << (w // 2 + 1))


def int_args(rng, op, w):
    r = lambda: rnd_int(rng, w)
    small = lambda: rng.randrange(0, 70)
    if op in ('isqrt', 'bit_length', 'abs', 'sign'): return [r()]
    if op == 'iroot': return [r(), rng.randrange(0, 9)]
    if op == 'ilog': return [r(), rng.choice([0, 1, 2, 3, 10, 16, r()])]
    if op == 'factorial': return [rng.choice([small(), r()])]
    if op in ('perm', 'comb'):
        n = rng.choice([small(), r(), rng.randrange(0, 1 << 12)])
        return [n, rng.choice([small(), rng.randrange(0, n + 2), r()])]
    if op in ('pow_mod',): return [r(), r(), rng.choice([0, 1, r(), (1 << w) - rng.randrange(1, 60)])]
    if op == 'mod_inverse': return [r(), rng.choice([0, 1, r(), (1 << w) - 59])]
    if op == 'divmod': return [r(), rng.choice([0, 1, r(), small()])]
    if op == 'clamp': return [r(), r(), r()]
    if op in ('gcd_all', 'lcm_all', 'prod', 'sum'): return [rng.choice([small(), r()]) for _ in range(rng.randrange(0, 6))]
    if op == 'pow': return [rng.choice([small(), r()]), rng.randrange(0, 70)]
    return [r(), r()]


def enc_int(v, w):
    return f'{v >> 32}_{v & 0xffffffff}' if w == 64 else str(v)


def show_int(e, w):
    if isinstance(e, str): return e
    if isinstance(e, tuple) and e[0] == 'N': return str(e[1])
    if isinstance(e, tuple) and e[0] == 'QR': return enc_int(e[1], w) + ',' + enc_int(e[2], w)
    return enc_int(e, w)


F32 = np.float32


def fbits(x):
    return str(int(np.array([x], dtype=F32).view(np.uint32)[0]))


def f_lt(a, b):
    return bool(a < b)


def f_expect(op, a):
    with np.errstate(all='ignore'):
        mn = lambda x, y: y if f_lt(y, x) else x
        mx = lambda x, y: y if f_lt(x, y) else x
        if op == 'clamp': return 'Domain' if f_lt(a[2], a[1]) else fbits(mn(mx(a[0], a[1]), a[2]))
        if op == 'min': return fbits(mn(a[0], a[1]))
        if op == 'max': return fbits(mx(a[0], a[1]))
        if op == 'abs': return fbits(np.abs(a[0]))
        if op == 'sign': return fbits(F32(1) if f_lt(F32(0), a[0]) else (F32(-1) if f_lt(a[0], F32(0)) else a[0]))
        if op in ('sum', 'prod'):
            r = F32(0) if op == 'sum' else F32(1)
            for x in a: r = F32(r + x) if op == 'sum' else F32(r * x)
            return fbits(r)
        if op == 'pow':
            x, k = a
            acc, base = F32(1), x
            while k > 0:
                if k & 1: acc = F32(acc * base)
                if k > 1: base = F32(base * base)
                k >>= 1
            return fbits(acc)
    raise ValueError(op)


def d_bits(x):
    v = struct.unpack('>Q', struct.pack('>d', x))[0]
    return f'{v >> 32}_{v & 0xffffffff}'


def d_expect(op, a):
    mn = lambda x, y: y if y < x else x
    mx = lambda x, y: y if x < y else x
    def mul(x, y):
        try: return x * y
        except OverflowError: return math.copysign(math.inf, x) * math.copysign(1.0, y)
    if op == 'clamp': return 'Domain' if a[2] < a[1] else d_bits(mn(mx(a[0], a[1]), a[2]))
    if op == 'min': return d_bits(mn(a[0], a[1]))
    if op == 'max': return d_bits(mx(a[0], a[1]))
    if op == 'abs': return d_bits(abs(a[0]))
    if op == 'sign': return d_bits(1.0 if 0.0 < a[0] else (-1.0 if a[0] < 0.0 else a[0]))
    if op in ('sum', 'prod'):
        r = 0.0 if op == 'sum' else 1.0
        for x in a: r = r + x if op == 'sum' else mul(r, x)
        return d_bits(r)
    if op == 'pow':
        x, k = a
        acc, base = 1.0, x
        while k > 0:
            if k & 1: acc = mul(acc, base)
            if k > 1: base = mul(base, base)
            k >>= 1
        return d_bits(acc)
    raise ValueError(op)


def rnd_d(rng):
    c = rng.random()
    if c < 0.05: return rng.choice([0.0, -0.0, math.inf, -math.inf, math.nan])
    if c < 0.1: return struct.unpack('>d', struct.pack('>Q', rng.randrange(1 << 64)))[0]
    if c < 0.6: return rng.uniform(-10, 10)
    return rng.uniform(-1, 1) * 10.0 ** rng.randrange(-300, 300)


def d_args(rng, op):
    if op in ('abs', 'sign'): return [rnd_d(rng)]
    if op == 'clamp': return [rnd_d(rng) for _ in range(3)]
    if op in ('sum', 'prod'): return [rnd_d(rng) for _ in range(rng.randrange(0, 6))]
    if op == 'pow': return [rnd_d(rng), rng.randrange(0, 40)]
    return [rnd_d(rng), rnd_d(rng)]


def nan_word(s):
    """a NaN of either float: "hi_lo" (binary64) or a decimal binary32 word"""
    if '_' in s:
        h, l = map(int, s.split('_'))
        return ((h >> 20) & 0x7ff) == 0x7ff and bool((h & 0xfffff) or l)
    if not s.isdigit(): return False
    w = int(s)
    return ((w >> 23) & 0xff) == 0xff and bool(w & 0x7fffff)


def rnd_f(rng):
    c = rng.random()
    if c < 0.05: return F32(rng.choice([0.0, -0.0, math.inf, -math.inf, math.nan]))
    if c < 0.1: return np.array([rng.randrange(0, 1 << 32)], dtype=np.uint32).view(F32)[0]
    if c < 0.6: return F32(rng.uniform(-10, 10))
    return F32(rng.uniform(-1, 1) * 10 ** rng.randrange(-40, 39))


def enc_f(x):
    if np.isnan(x): return 'nan'
    if np.isinf(x): return 'inf' if x > 0 else '-inf'
    return repr(float(x))


def f_args(rng, op):
    if op in ('abs', 'sign'): return [rnd_f(rng)]
    if op == 'clamp': return [rnd_f(rng) for _ in range(3)]
    if op in ('sum', 'prod'): return [rnd_f(rng) for _ in range(rng.randrange(0, 6))]
    if op == 'pow': return [rnd_f(rng), rng.randrange(0, 40)]
    return [rnd_f(rng), rnd_f(rng)]


def run(tokens):
    out = []
    for i in range(0, len(tokens), BATCH):
        chunk = tokens[i:i + BATCH]
        p = subprocess.run([str(BIN), '--threads', '1', '--'] + chunk, capture_output=True, text=True, timeout=600)
        lines = p.stdout.strip().split('\n') if p.stdout.strip() else []
        if len(lines) != len(chunk):
            raise SystemExit(f'driver printed {len(lines)} lines for {len(chunk)} tokens: {p.stderr[-400:]}')
        out += lines
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    rng = random.Random(seed)
    cases = []
    for ty, w in (('u32', 32), ('u64', 64)):
        for op in INT_OPS:
            for _ in range(per):
                a = int_args(rng, op, w)
                if op == 'pow': tok = f'{ty}:{op}:{enc_int(a[0], w)}:{a[1]}'
                elif op == 'iroot': tok = f'{ty}:{op}:{enc_int(a[0], w)}:{a[1]}'
                else: tok = ':'.join([ty, op] + [enc_int(x, w) for x in a])
                cases.append((tok, show_int(int_expect(op, a, w), w)))
    for op in F_OPS:
        for _ in range(per):
            a = f_args(rng, op)
            enc = [enc_f(a[0]), str(a[1])] if op == 'pow' else [enc_f(x) for x in a]
            cases.append((':'.join(['f32', op] + enc), f_expect(op, a)))
    if '--no-f64' not in sys.argv:
        for op in F_OPS:
            for _ in range(per):
                a = d_args(rng, op)
                enc = [d_bits(a[0]), str(a[1])] if op == 'pow' else [d_bits(x) for x in a]
                cases.append((':'.join(['f64', op] + enc), d_expect(op, a)))
    got = run([t for t, _ in cases])
    bad = [(t, e, g) for (t, e), g in zip(cases, got) if e != g and not (t.startswith(('f32', 'f64')) and nan_word(e) and nan_word(g))]
    print(json.dumps({'seed': seed, 'cases': len(cases), 'failures': len(bad), 'examples': bad[:12]}, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
