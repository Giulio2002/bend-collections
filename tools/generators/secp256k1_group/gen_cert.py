#!/usr/bin/env python3
"""Pocklington certificates for secp256k1's p (and n), as Bend files.

  python3 tools/generators/secp256k1_group/gen_cert.py

writes proofs/crypto/secp256k1/group/cert_*.bend. Nothing here is trusted:
the quotients, remainders, bases and Bezout witnesses computed below are
literals that the checker verifies with bn.bend's proved product, sum and
equality (bnx.bend), and the primality conclusion is ntpock.bend's theorem.
Needs sympy (for the factorizations of N - 1 only).
"""
import os, sys
from math import gcd
from sympy import factorint

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', '..', '..', 'proofs', 'crypto', 'secp256k1', 'group')
SMALL = 1500          # primes below this: trial division on the unary value
CHUNK = 48            # steps per closed check at 256 bits

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


CONSTS = {}     # value -> name, for the literals used more than once
CDEFS = []


def lit(v):
    """a big number by name (one def per distinct value), a small one inline"""
    if v < 2**20:
        return raw(v)
    if v not in CONSTS:
        CONSTS[v] = 'k%d' % len(CONSTS)
        CDEFS.append('def %s() -> B.Bn:\n  %s\n' % (CONSTS[v], raw(v)))
    return CONSTS[v] + '()'


def raw(v):
    s = 'B.BZ{}'
    bits = []
    while v:
        bits.append(v & 1)
        v >>= 1
    for b in reversed(bits):
        s = ('B.B1{%s}' if b else 'B.B0{%s}') % s
    return s


def steps(a, e, n):
    """the steps of a^e mod n (quotients only), with the residue and the exponent after each"""
    out, x, ex = [], a, 1
    for b in bin(e)[3:]:
        if b == '1':
            q, x = divmod(a * x * x, n)
            ex = 2 * ex + 1
            out.append(('X.SM{%s}' % raw(q), x, ex))
        else:
            q, x = divmod(x * x, n)
            ex = 2 * ex
            out.append(('X.Sq{%s}' % raw(q), x, ex))
    return out, x


def chunks(nm, a, e, n, defs):
    """defs nm_0.. proving CL.Inv(one, a, n, a^e mod n, e) chunk by chunk; returns the last def's name"""
    st, x = steps(a, e, n)
    size = max(16, int(CHUNK * (256 / n.bit_length()) ** 2))
    prev = 'CL.inv0(one, h1, %s, %s)' % (lit(a), lit(n))
    px, pe, last = a, 1, None
    for i in range(0, max(len(st), 1), size):
        part = st[i:i + size]
        cx, ce = (part[-1][1], part[-1][2]) if part else (px, pe)
        last = '%s_%d' % (nm, i // size)
        defs.append('def %s(+one: Nat, +h1: {one == 1n : Nat}) -> CL.Inv(one, %s, %s, %s, %s):\n  CL.ck_o(one, h1, %s, %s, %s, %s, %s, [%s], %s, %s, {==}, %s, {==}, {==})\n' % (
            last, lit(a), lit(n), lit(cx), lit(ce), lit(a), lit(n), lit(n - 1), lit(px), lit(pe), ', '.join(p[0] for p in part), lit(cx), lit(ce), prev))
        prev = '%s(one, h1)' % last
        px, pe = cx, ce
    assert pe == e and px == x
    return last, x


def plan(n):
    """the primes q of the factored part (exponent 1 in n - 1, largest first) and a base"""
    f = factorint(n - 1)
    qs, F = [], 1
    for q in sorted((q for q in f if f[q] == 1), reverse=True):
        qs.append(q)
        F *= q
        if F * F >= n:
            break
    assert F * F >= n, n
    a = 2
    while not (pow(a, n - 1, n) == 1 and all(gcd(pow(a, (n - 1) // q, n) - 1, n) == 1 and pow(a, (n - 1) // q, n) > 1 for q in qs)):
        a += 1
    return qs, a


def name(n):
    return 'p%d' % n if n < 10**9 else 'p%dx%d' % (n.bit_length(), n % 10**6)


def level(n, defs, done):
    """append the defs proving Prime(bvalo(one, lit(n))); returns the def's name"""
    nm = name(n)
    if n in done:
        return nm
    done.add(n)
    sig = 'def %s(+one: Nat, +h1: {one == 1n : Nat}) -> PM.Prime(X.bvalo(one, %s)):' % (nm, lit(n))
    if n < SMALL:
        defs.append('%s\n  CL.sp_o(one, h1, %s, {==})\n' % (sig, lit(n)))
        return nm
    qs, a = plan(n)
    subs = [level(q, defs, done) for q in qs]
    out = ['# %d = 1 + %s m, base %d' % (n, ' * '.join(str(q) for q in qs), a)]
    l3, x = chunks(nm + '_a', a, n - 1, n, out)
    assert x == 1
    cert = 'PK.cert_nil(X.bvalo(one, %s))' % lit(n)
    tail = 'Nil{}'
    fb, fh, F = 'B.B1{B.BZ{}}', 'X.one_o(one, h1)', 1      # the tail's product: Bn term, proof, value
    fnat = '1n'
    for i in range(len(qs) - 1, -1, -1):
        q = qs[i]
        m = (n - 1) // q
        b = pow(a, m, n)
        u = pow(b - 1, -1, n)
        v = (u * (b - 1) - 1) // n
        l4, x = chunks('%s_b%d' % (nm, i), a, m, n, out)
        assert x == b
        hq = '%s(one, h1)' % subs[i]
        e2 = 'X.e2_o(one, h1, %s, %s, %s, {==})' % (lit(n), lit(q), lit(m))
        e3 = 'CL.fin3_o(one, h1, %s, %s, %s, %s, %s, %s, %s, {==}, %s(one, h1), {==}, {==})' % (lit(a), lit(n), lit(n - 1), lit(n - 1), lit(q), lit(m), lit(n - 2), l3)
        e4 = 'CL.fin_o(one, h1, %s, %s, %s, %s, %s, %s, {==}, %s(one, h1), {==})' % (lit(a), lit(n), lit(n - 1), lit(b), lit(m), lit(n - 1 - b), l4)
        e5 = 'X.e5_o(one, h1, %s, %s, %s, %s, %s, {==}, {==})' % (lit(u), lit(b), lit(b - 1), lit(v), lit(n))
        if F == 1:
            e6 = 'X.e6_1(one, h1, %s, %s, {==})' % (lit(q), lit(q - 2))
        else:
            k, r = divmod(F, q)
            assert r > 0
            e6 = 'X.e6_o(one, h1, %s, %s, %s, %s, %s, %s, %s, {==}, {==})' % (fb, fnat, fh, lit(q), lit(k), lit(r - 1), lit(q - r - 1))
        ent = 'PK.PE{X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s)}' % (lit(q), lit(m), lit(a), lit(b), lit(u), lit(v))
        cert = 'PK.cert_cons(X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), X.bvalo(one, %s), %s, %s, %s, %s, %s, %s, %s, %s)' % (
            lit(n), lit(q), lit(m), lit(a), lit(b), lit(u), lit(v), tail, hq, e2, e3, e4, e5, e6, cert)
        tail = '%s <> %s' % (ent, tail)
        fh = 'X.fp_o(one, h1, %s, %s, %s, %s)' % (lit(q), fb, fnat, fh)
        fnat = 'Nat.mul(X.bvalo(one, %s), %s)' % (lit(q), fnat)
        fb = 'B.bmul(%s, %s)' % (lit(q), fb)
        F *= q
    hf = 'X.hf_o(one, h1, %s, %s, %s, %s, %s, {==})' % (lit(n), fb, fnat, fh, lit(F * F - n))
    out.append('%s\n  PK.pocklington(X.bvalo(one, %s), X.bvalo(one, %s), X.suc2_o(one, h1, %s, %s, {==}), %s, %s, %s)\n' % (
        sig, lit(n), lit(n - 2), lit(n), lit(n - 2), tail, cert, hf))
    defs.extend(out)
    return nm


HEAD = '''# GENERATED by tools/generators/secp256k1_group/gen_cert.py; edit the generator
import Base
import ./bn.bend as B
import ./bnx.bend as X
import ./certl.bend as CL
import ./prime.bend as PM
import ./ntpock.bend as PK

# Pocklington certificate: %s
# Every literal below (quotients and remainders of each squaring, bases,
# Bezout witnesses) is checked by closed computation on bn.bend's binary
# numbers; the numbers are X.bvalo(one, literal), never expanded.
'''


def write(fn, what, n):
    defs = []
    CONSTS.clear()
    del CDEFS[:]
    nm = level(n, defs, set())
    defs.append('def top() -> B.Bn:\n  %s\n' % lit(n))
    defs.append('def top_prime(+one: Nat, +h1: {one == 1n : Nat}) -> PM.Prime(X.bvalo(one, top())):\n  %s(one, h1)\n' % nm)
    open(os.path.join(OUT, fn), 'w').write(HEAD % what + '\n' + '\n'.join(CDEFS) + '\n' + '\n'.join(defs))
    return nm


def write_pow(fn, what, a, e, n):
    """a^e mod n as a chain of checked chunks: def pw proves CL.Inv(one, ca(), cn(), cc(), ce())"""
    defs = []
    CONSTS.clear()
    del CDEFS[:]
    last, x = chunks('c', a, e, n, defs)
    for nm, v in (('ca', a), ('cn', n), ('cc', x), ('ce', e)):
        defs.append('def %s() -> B.Bn:\n  %s\n' % (nm, lit(v)))
    defs.append('def pw(+one: Nat, +h1: {one == 1n : Nat}) -> CL.Inv(one, ca(), cn(), cc(), ce()):\n  %s(one, h1)\n' % last)
    open(os.path.join(OUT, fn), 'w').write(HEAD % what + '\n' + '\n'.join(CDEFS) + '\n' + '\n'.join(defs))
    return x


if __name__ == '__main__':
    which = sys.argv[1:] or ['p', 'c']
    if 'p' in which:
        print(write('cert_p.bend', 'p = 2^256 - 2^32 - 977 is prime', P))
    if 'n' in which:
        print(write('cert_n.bend', 'the group order n is prime', N))
    if 'c' in which:
        c = write_pow('cert_c.bend', '(p - 7)^((p - 1) / 3) mod p', P - 7, (P - 1) // 3, P)
        assert c != 1
        print('cube', c)
    for w in which:
        if w.isdigit():
            print(write('cert_t%s.bend' % w, 'test', int(w)))
