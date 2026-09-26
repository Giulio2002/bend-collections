#!/usr/bin/env python3
"""Differential test of src/math/natural.bend against CPython.

Random and edge-case inputs (every value and intermediate below Bend's
native Nat limit, 2^48) run through build/math/natural and are compared
with math.gcd/lcm/isqrt/factorial/perm/comb/prod, pow(b, e, m),
pow(a, -1, m), divmod and int.bit_length. Prints a JSON verdict.
"""
import json, math, random, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/natural'
LIM = 2 ** 48
BATCH = 400


def iroot(n, k):
    r = int(round(n ** (1.0 / k))) if n else 0
    while r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r


def ilog(n, b):
    k, p = 0, 1
    while p * b <= n:
        p, k = p * b, k + 1
    return k


def expect(op, a):
    try:
        if op == 'gcd': return str(math.gcd(a[0], a[1]))
        if op == 'lcm': return str(math.lcm(a[0], a[1]))
        if op == 'isqrt': return str(math.isqrt(a[0]))
        if op == 'iroot': return 'Domain' if a[1] == 0 else str(iroot(a[0], a[1]))
        if op == 'ilog': return 'Domain' if a[0] == 0 or a[1] < 2 else str(ilog(a[0], a[1]))
        if op == 'factorial': return str(math.factorial(a[0]))
        if op == 'perm': return str(math.perm(a[0], a[1]))
        if op == 'comb': return str(math.comb(a[0], a[1]))
        if op == 'pow_mod': return 'ZeroDivision' if a[2] == 0 else str(pow(a[0], a[1], a[2]))
        if op == 'mod_inverse':
            if a[1] == 0: return 'ZeroDivision'
            try: return str(pow(a[0], -1, a[1]))
            except ValueError: return 'NotInvertible'
        if op == 'divmod': return 'ZeroDivision' if a[1] == 0 else '%d,%d' % divmod(a[0], a[1])
        if op == 'bit_length': return str(a[0].bit_length())
        if op == 'clamp': return 'Domain' if a[2] < a[1] else str(min(max(a[0], a[1]), a[2]))
        if op == 'gcd_all': return str(math.gcd(*a))
        if op == 'lcm_all': return str(math.lcm(*a))
        if op == 'prod': return str(math.prod(a))
        if op == 'sum': return str(sum(a))
    except ZeroDivisionError:
        return 'ZeroDivision'
    raise KeyError(op)


def cases(rng):
    edge = [0, 1, 2, 3, 4, 7, 8, 15, 16, 255, 256, 1023, 1024, LIM - 1, LIM - 2, 2 ** 47, 2 ** 24, 2 ** 24 - 1]
    small = lambda: rng.choice([rng.randrange(20), rng.randrange(1000), rng.randrange(2 ** 24)])
    big = lambda: rng.choice(edge + [rng.randrange(LIM)] * 4)
    for _ in range(300):
        yield 'gcd', [big(), big()]
        a, b = rng.randrange(1, 2 ** 24), rng.randrange(2 ** 24)
        yield 'lcm', [a, b]
        yield 'isqrt', [big()]
        n, k = big(), rng.randrange(0, 8)
        if k == 0 or (iroot(n, k) + 1) ** k < LIM:
            yield 'iroot', [n, k]
        yield 'ilog', [big(), rng.choice([0, 1, 2, 3, 10, 16, rng.randrange(2, 1000)])]
        yield 'factorial', [rng.randrange(17)]
        n = rng.randrange(40)
        k = rng.randrange(n + 3)
        if math.perm(n, min(k, n)) < LIM:
            yield 'perm', [n, k]
        n = rng.randrange(50)
        k = rng.randrange(n + 3)
        if all(math.comb(n, i) * n < LIM for i in range(min(k, n) + 1)):
            yield 'comb', [n, k]
        m = rng.choice([0, 1, 2, rng.randrange(2, 2 ** 24)])
        yield 'pow_mod', [big(), rng.randrange(10 ** 6), m]
        yield 'mod_inverse', [small(), rng.choice([0, 1, 2, 12, rng.randrange(2, 2 ** 24)])]
        yield 'divmod', [big(), rng.choice([0, 1, 2, small(), big()])]
        yield 'bit_length', [big()]
        yield 'clamp', [small(), small(), small()]
        xs = [rng.randrange(2 ** 20) for _ in range(rng.randrange(5))]
        yield 'gcd_all', xs
        yield 'lcm_all', [rng.randrange(1, 40) for _ in range(rng.randrange(4))]
        yield 'prod', [rng.randrange(1, 100) for _ in range(rng.randrange(5))]
        yield 'sum', xs


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    todo = list(cases(rng))
    fails = []
    for i in range(0, len(todo), BATCH):
        chunk = todo[i:i + BATCH]
        toks = [':'.join([op] + [str(x) for x in a]) for op, a in chunk]
        p = subprocess.run([str(BIN)] + toks, capture_output=True, text=True, timeout=600)
        got = p.stdout.split('\n')
        for (op, a), g in zip(chunk, got + [''] * len(chunk)):
            e = expect(op, a)
            if g.strip() != e:
                fails.append({'op': op, 'args': a, 'expected': e, 'got': g.strip()})
    ops = sorted({op for op, _ in todo})
    print(json.dumps({'passed': not fails, 'cases': len(todo), 'operations': ops, 'failures': fails[:20]}, indent=1))
    return 0 if not fails else 1


if __name__ == '__main__':
    sys.exit(main())
