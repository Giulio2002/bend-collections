#!/usr/bin/env python3
"""Generate the Poly1305 run-time bound proofs (every Nat the limb code
computes is below 2^48, Bend's native Nat range).

  python3 tools/generators/poly1305_safe.py

writes proofs/crypto/poly1305/sops.bend (one predicate per limb function:
ok_F(args) is the conjunction of C.fits(48n, v) over every value v the
function's body computes, and F_ok proves it under the function's
precondition; F_fit proves the postcondition, F_mirror checks by {==} that
the expressions ok_F talks about are the function's body) and
proofs/crypto/poly1305/safe.bend (the same over the message loops, the tag
and the AEAD tag, for every key and message).

Nothing here is trusted: the bit widths below are what the generated
lemmas claim, and the checker verifies every step. A width over 48 stops
the generator.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, 'proofs', 'crypto', 'poly1305')
MAC_SRC = os.path.join(ROOT, 'tools', 'generators', 'poly1305_hand', 'mac.src')

T = '{C.fits(%dn, %s) == True{} : Bool}'


def fits(k, x):
    return T % (k, x)


class Nd:
    def __init__(s, e, full, bits, p):
        s.e, s.full, s.bits, s.p = e, full, bits, p


def fm(n, k):
    """a proof that n fits k bits (k >= n.bits)"""
    if n.bits == k:
        return n.p
    assert n.bits < k, (n.full, n.bits, k)
    return 'B.fm(%dn, %dn, %s, {==}, %s)' % (n.bits, k, n.e, n.p)


LOG = {4: 2, 16: 4, 64: 6, 256: 8, 8192: 13}
DIV = {4: 'K.fd4', 16: 'K.fd16', 64: 'K.fd64', 256: 'K.fd256', 8192: 'K.fdb'}
MOD = {4: 'K.fm4', 16: 'K.fm16', 64: 'K.fm64', 256: 'K.fm256', 8192: 'K.fmb'}


class U:
    """one function body: its values (lets), their widths and proofs, and
    the atoms of its ok predicate"""

    def __init__(s):
        s.lets = []      # (name, expr) values, shared by predicate and proof
        s.plets = []     # (name, proof)
        s.atoms = []     # (formula, proof)
        s.i = 0

    def fresh(s):
        s.i += 1
        return s.i

    def val(s, expr, full, bits, proof, atom=True):
        assert bits <= 48, (full, bits)
        k = s.fresh()
        t, p = 'v%d' % k, 'w%d' % k
        s.lets.append((t, expr))
        s.plets.append((p, proof))
        n = Nd(t, full, bits, p)
        if atom:
            s.atoms.append(('C.fits(48n, %s)' % t, fm(n, 48)))
        return n

    def var(s, name, bits, proof):
        return Nd(name, name, bits, proof)

    def lit(s, v):
        return Nd('%dn' % v, '%dn' % v, v.bit_length(), '{==}')

    def add(s, a, b):
        if a.bits >= b.bits:
            pr = 'B.fa(%dn, %dn, %s, %s, {==}, %s, %s)' % (a.bits, b.bits, a.e, b.e, a.p, b.p)
        else:
            pr = 'B.fb(%dn, %dn, %s, %s, {==}, %s, %s)' % (b.bits, a.bits, a.e, b.e, a.p, b.p)
        return s.val('Nat.add(%s, %s)' % (a.e, b.e), 'Nat.add(%s, %s)' % (a.full, b.full), 1 + max(a.bits, b.bits), pr)

    def mul(s, a, b):
        pr = 'A.fits_mul(%dn, %dn, %s, %s, %s, %s)' % (a.bits, b.bits, a.e, b.e, a.p, b.p)
        return s.val('Nat.mul(%s, %s)' % (a.e, b.e), 'Nat.mul(%s, %s)' % (a.full, b.full), a.bits + b.bits, pr)

    def _hin(s, a, k):
        if a.bits == k:
            return a.p
        if a.bits < k:
            return 'B.fm(%dn, %dn, %s, {==}, %s)' % (a.bits, k, a.e, a.p)
        raise AssertionError

    def div(s, a, c):
        l = LOG[c]
        j = max(a.bits - l, 0)
        pr = '%s(%dn, %s, %s)' % (DIV[c], j, a.e, s._hin(a, l + j))
        return s.val('Nat.div(%s, %dn)' % (a.e, c), 'Nat.div(%s, %dn)' % (a.full, c), j, pr)

    def mod(s, a, c):
        return s.val('Nat.mod(%s, %dn)' % (a.e, c), 'Nat.mod(%s, %dn)' % (a.full, c), LOG[c], '%s(%s)' % (MOD[c], a.e))

    def sub1(s, c):
        return s.val('Nat.sub(1n, %s)' % c.e, 'Nat.sub(1n, %s)' % c.full, 1, 'fsub1(%s)' % c.e)

    def h48(s, a):
        return fm(a, 48)

    # calls of the helper functions: their values are in their own ok
    def dw(s, a):
        j = max(a.bits - 26, 0)
        s.atoms.append(('ok_dw(%s)' % a.e, 'dw_ok(%s, %s)' % (a.e, s.h48(a))))
        return s.val('L.dw(%s)' % a.e, 'L.dw(%s)' % a.full, j, 'K.fdw(%dn, %s, %s)' % (j, a.e, s._hin(a, 26 + j)), atom=False)

    def mw(s, a):
        s.atoms.append(('ok_mw(%s)' % a.e, 'mw_ok(%s, %s)' % (a.e, s.h48(a))))
        return s.val('L.mw(%s)' % a.e, 'L.mw(%s)' % a.full, 26, 'K.fmw(%s)' % a.e, atom=False)

    def d8(s, a):
        j = max(a.bits - 8, 0)
        return s.val('L.d8(%s)' % a.e, 'L.d8(%s)' % a.full, j, 'K.fd256(%dn, %s, %s)' % (j, a.e, s._hin(a, 8 + j)))

    def by(s, a):
        s.atoms.append(('ok_by(%s)' % a.e, 'by_ok(%s)' % a.e))
        return 'L.by(%s)' % a.full

    def pick(s, c, x, y):
        args = (c.e, x.e, y.e, s._hin(c, 2), s._hin(x, 27), s._hin(y, 26))
        s.atoms.append(('ok_pick(%s, %s, %s)' % (c.e, x.e, y.e), 'pick_ok(%s, %s, %s, %s, %s, %s)' % args))
        return s.val('L.pick(%s, %s, %s)' % (c.e, x.e, y.e), 'L.pick(%s, %s, %s)' % (c.full, x.full, y.full), 29, 'pick_fit(%s, %s, %s, %s, %s, %s)' % args, atom=False)

    def call(s, pred, lemma, args, hyps):
        """a call of another generated unit, whose values are its own ok"""
        s.atoms.append(('%s(%s)' % (pred, ', '.join(a.e for a in args)),
                        '%s(%s)' % (lemma, ', '.join([a.e for a in args] + [s._hin(a, k) for a, k in zip(args, hyps)]))))

    def conj(s):
        if not s.atoms:
            return 'True{}', ['{==}'], []
        fs = [a[0] for a in s.atoms]
        e = fs[-1]
        for f in reversed(fs[:-1]):
            e = 'Bool.and(%s, %s)' % (f, e)
        # the proof: c_i the conjunction from i on, q_i its proof
        n = len(fs)
        lines = []
        lines.append('+c%d = %s' % (n - 1, fs[-1]))
        for i in range(n - 2, -1, -1):
            lines.append('+c%d = Bool.and(%s, c%d)' % (i, fs[i], i + 1))
        lines.append('+q%d = %s' % (n - 1, s.atoms[-1][1]))
        for i in range(n - 2, -1, -1):
            lines.append('+q%d = LG.and_intro(%s, c%d, %s, q%d)' % (i, fs[i], i + 1, s.atoms[i][1], i + 1))
        return e, lines, 'q0'


def nat_params(names):
    return ', '.join('+%s: Nat' % n for n in names)


def fit_params(names, bits):
    return ', '.join('+h%s: %s' % (n, fits(b, n)) for n, b in zip(names, bits))


def F(ls):
    return 'L.F{%s}' % ', '.join(ls)


def emit_unit(out, name, params, bits, build, record=None, rbits=None, mirror_lhs=None, mirror_ty=None, fit=None):
    """params: Nat parameter names (the limbs of the records, in order);
    record: list of (record var, [limb names]) when the function takes L.F
    records; build(u, nodes) -> (mirror rhs, fit list [(k, node)] or None)"""
    u = U()
    nodes = [u.var(n, b, 'h' + n) for n, b in zip(params, bits)]
    rhs, fitl = build(u, nodes)
    e, clines, q = u.conj()
    body_lets = ['+%s = %s' % (t, x) for t, x in u.lets]
    # predicate
    if record:
        sig = ', '.join('%s: L.F' % r for r, _ in record)
        out.append('def ok_%s(%s) -> Bool:' % (name, sig))
        out.append('  match %s:' % ' '.join(r for r, _ in record))
        out.append('    case %s:' % ' '.join(F(['+' + x for x in ls]) for _, ls in record))
        ind = '      '
    else:
        out.append('def ok_%s(%s) -> Bool:' % (name, nat_params(params)))
        ind = '  '
    for l in body_lets:
        out.append(ind + l)
    out.append(ind + e)
    out.append('')
    # args of the predicate for the limb lemma
    if record:
        pargs = ', '.join(F(ls) for _, ls in record)
    else:
        pargs = ', '.join(params)
    # mirror
    if mirror_lhs:
        out.append('def %s_mirror(%s) -> {%s == %s : %s}:' % (name, nat_params(params), mirror_lhs, rhs, mirror_ty))
        out.append('  {==}')
        out.append('')
    # ok lemma
    out.append('def %s_ok(%s, %s) -> {ok_%s(%s) == True{} : Bool}:' % (name, nat_params(params), fit_params(params, bits), name, pargs))
    for (t, x), (p, pr) in zip(u.lets, u.plets):
        out.append('  +%s = %s' % (t, x))
        out.append('  +%s = %s' % (p, pr))
    for l in clines:
        out.append('  ' + l)
    out.append('  ' + q)
    out.append('')
    # fit lemma
    if fit:
        fk, fty, fproof = fit(u, nodes, fitl)
        out.append('def %s_fit(%s, %s) -> {%s == True{} : Bool}:' % (name, nat_params(params), fit_params(params, bits), fty))
        for (t, x), (p, pr) in zip(u.lets, u.plets):
            out.append('  +%s = %s' % (t, x))
            out.append('  +%s = %s' % (p, pr))
        out.append('  ' + fproof)
        out.append('')
    # record wrappers
    if record:
        rsig = ', '.join('%s: L.F' % r for r, _ in record)
        rb = {}
        idx = 0
        hyps = []
        for r, ls in record:
            k = bits[idx]
            assert all(b == k for b in bits[idx:idx + len(ls)])
            rb[r] = k
            idx += len(ls)
            hyps.append('+h%s: {B.lim(%dn, %s) == True{} : Bool}' % (r, k, r))
        getters = []
        for r, ls in record:
            for i, _ in enumerate(ls):
                getters.append('B.g%d(%dn, %s, h%s)' % (i, rb[r], ', '.join(ls), r))
        rargs = ', '.join(r for r, _ in record)
        for kind, ty in [('ok', 'ok_%s(%s)' % (name, rargs))] + ([('fit', fit_r_ty(name, rargs, fk))] if fit else []):
            out.append('def %s_%s_r(%s, %s) -> {%s == True{} : Bool}:' % (name, kind, rsig, ', '.join(hyps), ty))
            out.append('  match %s:' % ' '.join(r for r, _ in record))
            out.append('    case %s:' % ' '.join(F(['+' + x for x in ls]) for _, ls in record))
            out.append('      %s_%s(%s, %s)' % (name, kind, ', '.join(params), ', '.join(getters)))
            out.append('')
    return u


def fit_r_ty(name, rargs, fk):
    return 'B.lim(%dn, L.%s(%s))' % (fk, name, rargs)


def lim_fit(k, call):
    """fit: every output limb (a node) fits k bits: B.lim(k, L.f(..))"""
    def f(u, nodes, outs):
        ps = ', '.join(o.e for o in outs)
        prs = ', '.join(fm(o, k) for o in outs)
        return k, 'B.lim(%dn, %s)' % (k, call(nodes)), 'B.mk(%dn, %s, %s)' % (k, ps, prs)
    return f


# ---------------------------------------------------------------- units

def b_dw(u, n):
    x, = n
    a = u.div(x, 8192)
    b = u.div(a, 8192)
    return b.full, None


def b_mw(u, n):
    x, = n
    a = u.mod(x, 8192)
    b = u.div(x, 8192)
    c = u.mod(b, 8192)
    d = u.mul(c, u.lit(8192))
    e = u.add(a, d)
    return e.full, None


def b_pick(u, n):
    c, x, y = n
    s1 = u.sub1(c)
    a = u.mul(x, s1)
    b = u.mul(y, c)
    r = u.add(a, b)
    return r.full, [r]


def b_mul(u, n):
    a = n[0:5]
    r = n[5:10]
    s = [None] + n[10:14]
    cols = []
    for k in range(5):
        terms = []
        for i in range(5):
            j = k - i
            terms.append(u.mul(a[i], r[j] if j >= 0 else s[5 + j]))
        # a0 r_k + (a1 . + (a2 . + (a3 . + a4 .)))
        acc = u.add(terms[3], terms[4])
        acc = u.add(terms[2], acc)
        acc = u.add(terms[1], acc)
        acc = u.add(terms[0], acc)
        cols.append(acc)
    return F([c.full for c in cols]), cols


def b_comb(u, n):
    d = n[0:5]
    e = n[5:10]
    b = u.lit(8192)
    five = u.lit(5)
    outs = []
    for i in range(5):
        lo = u.mul(u.mw(e[i]), b)
        if i == 0:
            hi = u.mul(u.mul(u.dw(e[4]), b), five)
        else:
            hi = u.mul(u.dw(e[i - 1]), b)
        outs.append(u.add(d[i], u.add(lo, hi)))
    return F([o.full for o in outs]), outs


def b_top(u, n):
    z0, z1, z2, z3, z4 = n
    y1 = u.add(z1, u.dw(z0))
    y2 = u.add(z2, u.dw(y1))
    y3 = u.add(z3, u.dw(y2))
    y4 = u.add(z4, u.dw(y3))
    l0 = u.add(u.mw(z0), u.mul(u.dw(y4), u.lit(5)))
    outs = [l0, u.mw(y1), u.mw(y2), u.mw(y3), u.mw(y4)]
    return F([o.full for o in outs]), outs


def b_fix(u, n):
    u0, t1, t2, t3, t4 = n
    a = u.mw(u0)
    b = u.add(t1, u.dw(u0))
    return F([a.full, b.full, t2.full, t3.full, t4.full]), None


def b_key(u, n):
    r = n
    e = [u.mod(x, 8192) for x in r]
    o = [u.div(x, 8192) for x in r]
    f = [u.mul(x, u.lit(5)) for x in e[1:]]
    g = [u.mul(x, u.lit(5)) for x in o[1:]]
    return 'L.K{%s}' % ', '.join(x.full for x in e + f + o + g), None


def load_exprs(x, pb, mk):
    """the limbs of L.load, built with mk = (add, mul, mod, div, lit)"""
    add, mul, mod, div, lit = mk
    c256 = lambda: lit(256)
    l0 = add(x[0], mul(add(x[1], mul(add(x[2], mul(mod(x[3], 4), c256())), c256())), c256()))
    l1 = add(div(x[3], 4), mul(add(x[4], mul(add(x[5], mul(mod(x[6], 16), c256())), c256())), lit(64)))
    l2 = add(div(x[6], 16), mul(add(x[7], mul(add(x[8], mul(mod(x[9], 64), c256())), c256())), lit(16)))
    l3 = add(div(x[9], 64), mul(add(x[10], mul(add(x[11], mul(x[12], c256())), c256())), lit(4)))
    l4 = add(x[13], mul(add(x[14], mul(add(x[15], mul(pb, c256())), c256())), c256()))
    return [l0, l1, l2, l3, l4]


def b_load(u, n):
    x = n[:16]
    pb = n[16]
    outs = load_exprs(x, pb, (u.add, u.mul, u.mod, u.div, u.lit))
    return F([o.full for o in outs]), outs


def load_strs(x, pb):
    """the limbs of L.load(x.., pb) as strings"""
    return load_exprs(x, pb, (lambda a, b: 'Nat.add(%s, %s)' % (a, b), lambda a, b: 'Nat.mul(%s, %s)' % (a, b),
                              lambda a, c: 'Nat.mod(%s, %dn)' % (a, c), lambda a, c: 'Nat.div(%s, %dn)' % (a, c), lambda v: '%dn' % v))


BYTES_L4 = []


def b_frz(u, n):
    h = n[0:5]
    s = n[5:10]
    g0 = u.add(h[0], u.lit(5))
    g1 = u.add(h[1], u.dw(g0))
    g2 = u.add(h[2], u.dw(g1))
    g3 = u.add(h[3], u.dw(g2))
    g4 = u.add(h[4], u.dw(g3))
    c = u.dw(g4)
    t0 = u.add(u.pick(c, h[0], u.mw(g0)), s[0])
    t1 = u.add(u.add(u.pick(c, h[1], u.mw(g1)), s[1]), u.dw(t0))
    t2 = u.add(u.add(u.pick(c, h[2], u.mw(g2)), s[2]), u.dw(t1))
    t3 = u.add(u.add(u.pick(c, h[3], u.mw(g3)), s[3]), u.dw(t2))
    t4 = u.add(u.add(u.pick(c, h[4], u.mw(g4)), s[4]), u.dw(t3))
    args = [u.mw(t0), u.mw(t1), u.mw(t2), u.mw(t3), t4]
    BYTES_L4.append(t4.bits)
    u.call('ok_bytes', 'bytes_ok', args, [26, 26, 26, 26, BYTES_BITS])
    return 'L.bytes(%s)' % ', '.join(a.full for a in args), None


BYTES_BITS = 32


def b_bytes(u, n):
    l0, l1, l2, l3, l4 = n
    d8 = u.d8
    a1 = d8(l0)
    a2 = d8(a1)
    c0 = u.add(d8(a2), u.mul(l1, u.lit(4)))
    c1 = d8(c0)
    c2 = d8(c1)
    q0 = u.add(d8(c2), u.mul(l2, u.lit(16)))
    q1 = d8(q0)
    q2 = d8(q1)
    t0 = u.add(d8(q2), u.mul(l3, u.lit(64)))
    t1 = d8(t0)
    t2 = d8(t1)
    t3 = d8(t2)
    u0 = u.add(d8(t3), l4)
    u1 = d8(u0)
    last = d8(u1)
    bs = [u.by(x) for x in [l0, a1, a2, c0, c1, c2, q0, q1, q2, t0, t1, t2, t3, u0, u1, last]]
    return '[%s]' % ', '.join(bs), None


# ---------------------------------------------------------------- sops.bend

HEAD = '''import Base
import ../../../spec/lib/common.bend as C
import ../../../src/crypto/poly1305/limbs.bend as L
import ../../lib/logic.bend as LG
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ./arith.bend as A
import ./nat.bend as K
import ./bnd.bend as B

# Generated by tools/generators/poly1305_safe.py (do not edit).
#
# Run-time bounds of the radix-2^26 limb code (src/crypto/poly1305/
# limbs.bend). Bend's native Nat is one machine word and aborts past 2^48,
# so every value a limb function computes must be below 2^48. For each
# function f, ok_f(args) is the conjunction of C.fits(48n, v) over every
# value v its body computes (every sum, product, quotient, remainder and
# difference; a call of dw, mw, pick or bytes contributes that function's
# ok), f_mirror checks by {==} that these are the expressions of f's body,
# f_ok proves ok_f under f's precondition (limb widths) and f_fit proves
# f's postcondition. The widths are the bounded-limbs invariant of HACL*'s
# Field32xN / Fiat-Crypto, restated for 13-bit multiplier halves:
#
#   accumulator h (between blocks)    27 bits per limb
#   message block m, key r, s         26 bits per limb (the pad bit at 2^128: limb 4)
#   h + m                             28
#   multiplier halves e, o            13 (5 e, 5 o: 16)
#   product columns (mul)             46 (precise: 1 + 4 * 5 < 32 products of 41 bits;
#                                         every partial sum at most 48)
#   combined columns (comb)           47
#   carry chains (top)                48, out: 27
#
# The precise column bound is mul_col (sum5 over terms below 6 * 2^41).

# x - 1 for x <= 1: 0 or 1
def fsub1(+c: Nat) -> {C.fits(1n, Nat.sub(1n, c)) == True{} : Bool}:
  match c:
    case 0n: {==}
    case 1n+p:
      match p:
        case 0n: {==}
        case 1n+q: {==}

# a < 2^ka, r < 2^kr: a r < 6 * 2^(ka + kr)
def tr6(+ka: Nat, +kr: Nat, +a: Nat, +r: Nat, +ha: {C.fits(ka, a) == True{} : Bool}, +hr: {C.fits(kr, r) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, r), Nat.mul(C.pow2(Nat.add(ka, kr)), 6n)) == True{} : Bool}:
  +p = C.pow2(Nat.add(ka, kr))
  +s1 = A.lt_subst(Nat.mul(a, r), Nat.mul(C.pow2(ka), C.pow2(kr)), p, A.pow2_add(ka, kr), A.lt_mul(a, r, C.pow2(ka), C.pow2(kr), WW.lt_of_fits(ka, a, ha), WW.lt_of_fits(kr, r, hr)))
  N.lt_le_trans(Nat.mul(a, r), p, Nat.mul(p, 6n), s1, A.le_substl(Nat.mul(p, 1n), p, Nat.mul(p, 6n), NA.mul_one(p), WM.le_mul_r(p, 1n, 6n, {==})))

# a < 2^ka, r < 2^kr: a (5 r) < 6 * 2^(ka + kr)
def ts6(+ka: Nat, +kr: Nat, +a: Nat, +r: Nat, +ha: {C.fits(ka, a) == True{} : Bool}, +hr: {C.fits(kr, r) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, Nat.mul(r, 5n)), Nat.mul(C.pow2(Nat.add(ka, kr)), 6n)) == True{} : Bool}:
  +pa = C.pow2(ka)
  +pr = C.pow2(kr)
  +s1 = A.lt_mul(r, 5n, pr, 6n, WW.lt_of_fits(kr, r, hr), {==})
  +s2 = A.lt_mul(a, Nat.mul(r, 5n), pa, Nat.mul(pr, 6n), WW.lt_of_fits(ka, a, ha), s1)
  +e = A.tr(Nat.mul(pa, Nat.mul(pr, 6n)), Nat.mul(Nat.mul(pa, pr), 6n), Nat.mul(C.pow2(Nat.add(ka, kr)), 6n), A.sy(Nat.mul(Nat.mul(pa, pr), 6n), Nat.mul(pa, Nat.mul(pr, 6n)), NA.mul_assoc(pa, pr, 6n)), Equal.cong(Nat, Nat, z => Nat.mul(z, 6n), Nat.mul(pa, pr), C.pow2(Nat.add(ka, kr)), A.pow2_add(ka, kr)))
  A.lt_subst(Nat.mul(a, Nat.mul(r, 5n)), Nat.mul(pa, Nat.mul(pr, 6n)), Nat.mul(C.pow2(Nat.add(ka, kr)), 6n), e, s2)

# p x + p y == p (x + y)
def pa2(+p: Nat, +x: Nat, +y: Nat) -> {Nat.add(Nat.mul(p, x), Nat.mul(p, y)) == Nat.mul(p, Nat.add(x, y)) : Nat}:
  A.sy(Nat.mul(p, Nat.add(x, y)), Nat.add(Nat.mul(p, x), Nat.mul(p, y)), NA.mul_add_left(p, x, y))

# five terms below 6 p: their sum (as a column of mul) is below 32 p
def sum5(+p: Nat, +y0: Nat, +y1: Nat, +y2: Nat, +y3: Nat, +y4: Nat, +h0: {Nat.is_lt(y0, Nat.mul(p, 6n)) == True{} : Bool}, +h1: {Nat.is_lt(y1, Nat.mul(p, 6n)) == True{} : Bool}, +h2: {Nat.is_lt(y2, Nat.mul(p, 6n)) == True{} : Bool}, +h3: {Nat.is_lt(y3, Nat.mul(p, 6n)) == True{} : Bool}, +h4: {Nat.is_lt(y4, Nat.mul(p, 6n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(y0, Nat.add(y1, Nat.add(y2, Nat.add(y3, y4)))), Nat.mul(p, 32n)) == True{} : Bool}:
  +q6 = Nat.mul(p, 6n)
  +s3 = A.lt_subst(Nat.add(y3, y4), Nat.add(q6, q6), Nat.mul(p, 12n), pa2(p, 6n, 6n), A.lt_add2(y3, y4, q6, q6, h3, h4))
  +w3 = Nat.add(y3, y4)
  +s2 = A.lt_subst(Nat.add(y2, w3), Nat.add(q6, Nat.mul(p, 12n)), Nat.mul(p, 18n), pa2(p, 6n, 12n), A.lt_add2(y2, w3, q6, Nat.mul(p, 12n), h2, s3))
  +w2 = Nat.add(y2, w3)
  +s1 = A.lt_subst(Nat.add(y1, w2), Nat.add(q6, Nat.mul(p, 18n)), Nat.mul(p, 24n), pa2(p, 6n, 18n), A.lt_add2(y1, w2, q6, Nat.mul(p, 18n), h1, s2))
  +w1 = Nat.add(y1, w2)
  +s0 = A.lt_subst(Nat.add(y0, w1), Nat.add(q6, Nat.mul(p, 24n)), Nat.mul(p, 30n), pa2(p, 6n, 24n), A.lt_add2(y0, w1, q6, Nat.mul(p, 24n), h0, s1))
  N.lt_le_trans(Nat.add(y0, w1), Nat.mul(p, 30n), Nat.mul(p, 32n), s0, WM.le_mul_r(p, 30n, 32n, {==}))

# a column below 32 p fits 5 + (ka + kr) bits, p = 2^(ka + kr)
def col5(+ka: Nat, +kr: Nat, +x: Nat, +h: {Nat.is_lt(x, Nat.mul(C.pow2(Nat.add(ka, kr)), 32n)) == True{} : Bool}) -> {C.fits(5n+Nat.add(ka, kr), x) == True{} : Bool}:
  +p = C.pow2(Nat.add(ka, kr))
  WW.fits_of_lt(5n+Nat.add(ka, kr), x, A.lt_subst(x, Nat.mul(p, 32n), C.shift(5n, p), A.mul_pow(5n, p), h))

# a limb width lowered to a looser one
def lim_mono(+j: Nat, +k: Nat, +hj: {Nat.is_le(j, k) == True{} : Bool}, f: L.F, +h: {B.lim(j, f) == True{} : Bool}) -> {B.lim(k, f) == True{} : Bool}:
  match f:
    case L.F{+l0, +l1, +l2, +l3, +l4}:
      B.mk(k, l0, l1, l2, l3, l4, B.fm(j, k, l0, hj, B.g0(j, l0, l1, l2, l3, l4, h)), B.fm(j, k, l1, hj, B.g1(j, l0, l1, l2, l3, l4, h)), B.fm(j, k, l2, hj, B.g2(j, l0, l1, l2, l3, l4, h)), B.fm(j, k, l3, hj, B.g3(j, l0, l1, l2, l3, l4, h)), B.fm(j, k, l4, hj, B.g4(j, l0, l1, l2, l3, l4, h)))

# the low byte of x (L.by's value)
def ok_by(+x: Nat) -> Bool:
  C.fits(48n, Nat.mod(x, 256n))

def by_ok(+x: Nat) -> {ok_by(x) == True{} : Bool}:
  B.fm(8n, 48n, Nat.mod(x, 256n), {==}, K.fm256(x))

'''


def mul_col():
    """mul's columns fit 5 + (ka + kr) bits (ka = 28, kr = 13 at the call: 46)"""
    a = ['a%d' % i for i in range(5)]
    r = ['r%d' % i for i in range(5)]
    s = [None] + ['Nat.mul(r%d, 5n)' % i for i in range(1, 5)]
    L_ = []
    ps = ', '.join('+%s: Nat' % x for x in a + r)
    hs = ', '.join('+h%s: {C.fits(ka, %s) == True{} : Bool}' % (x, x) for x in a) + ', ' + ', '.join('+h%s: {C.fits(kr, %s) == True{} : Bool}' % (x, x) for x in r)
    call = 'L.mul(%s, %s)' % (', '.join(a + r), ', '.join(s[1:]))
    L_.append('def mul_col(+ka: Nat, +kr: Nat, %s, %s) -> {B.lim(5n+Nat.add(ka, kr), %s) == True{} : Bool}:' % (ps, hs, call))
    L_.append('  +p = C.pow2(Nat.add(ka, kr))')
    cols = []
    for k in range(5):
        ys, prs = [], []
        for i in range(5):
            j = k - i
            if j >= 0:
                ys.append('Nat.mul(a%d, r%d)' % (i, j))
                prs.append('tr6(ka, kr, a%d, r%d, ha%d, hr%d)' % (i, j, i, j))
            else:
                ys.append('Nat.mul(a%d, Nat.mul(r%d, 5n))' % (i, 5 + j))
                prs.append('ts6(ka, kr, a%d, r%d, ha%d, hr%d)' % (i, 5 + j, i, 5 + j))
        col = 'Nat.add(%s, Nat.add(%s, Nat.add(%s, Nat.add(%s, %s))))' % tuple(ys)
        L_.append('  +x%d = %s' % (k, col))
        L_.append('  +f%d = col5(ka, kr, x%d, sum5(p, %s, %s))' % (k, k, ', '.join(ys), ', '.join(prs)))
        cols.append('x%d' % k)
    L_.append('  B.mk(5n+Nat.add(ka, kr), %s, %s)' % (', '.join(cols), ', '.join('f%d' % k for k in range(5))))
    L_.append('')
    return L_


def gen_sops():
    out = [HEAD]
    lim = lambda k, n: [k] * n
    # helpers first
    emit_unit(out, 'dw', ['x'], [48], b_dw, mirror_lhs='L.dw(x)', mirror_ty='Nat')
    emit_unit(out, 'mw', ['x'], [48], b_mw, mirror_lhs='L.mw(x)', mirror_ty='Nat')
    emit_unit(out, 'pick', ['c', 'x', 'y'], [2, 27, 26], b_pick, mirror_lhs='L.pick(c, x, y)', mirror_ty='Nat',
              fit=lambda u, n, o: (29, 'C.fits(29n, L.pick(c, x, y))', o[0].p))
    # bytes: its l4 width comes from frz, generated first into a scratch list
    scratch = []
    emit_unit(scratch, 'frz', ['h0', 'h1', 'h2', 'h3', 'h4', 's0', 's1', 's2', 's3', 's4'], [27] * 5 + [26] * 5, b_frz)
    global BYTES_BITS
    BYTES_BITS = BYTES_L4[-1]
    ls = ['l0', 'l1', 'l2', 'l3', 'l4']
    emit_unit(out, 'bytes', ls, [26, 26, 26, 26, BYTES_BITS], b_bytes, mirror_lhs='L.bytes(%s)' % ', '.join(ls), mirror_ty='List<&2, U32>')
    hs = ['h0', 'h1', 'h2', 'h3', 'h4']
    ss = ['s0', 's1', 's2', 's3', 's4']
    emit_unit(out, 'frz', hs + ss, [27] * 5 + [26] * 5, b_frz, record=[('h', hs), ('s', ss)],
              mirror_lhs='L.frz(%s, %s)' % (F(hs), F(ss)), mirror_ty='List<&2, U32>')
    a = ['a%d' % i for i in range(5)]
    r = ['r%d' % i for i in range(5)]
    s = ['s%d' % i for i in range(1, 5)]
    emit_unit(out, 'mul', a + r + s, [28] * 5 + [13] * 5 + [16] * 4, b_mul, mirror_lhs='L.mul(%s)' % ', '.join(a + r + s), mirror_ty='L.F')
    out.extend(mul_col())
    d = ['d%d' % i for i in range(5)]
    e = ['e%d' % i for i in range(5)]
    emit_unit(out, 'comb', d + e, [46] * 10, b_comb, record=[('d', d), ('e', e)], mirror_lhs='L.comb(%s, %s)' % (F(d), F(e)), mirror_ty='L.F',
              fit=lim_fit(47, lambda n: 'L.comb(%s, %s)' % (F(d), F(e))))
    z = ['z%d' % i for i in range(5)]
    emit_unit(out, 'top', z, [47] * 5, b_top, record=[('z', z)], mirror_lhs='L.top(%s)' % F(z), mirror_ty='L.F',
              fit=lim_fit(27, lambda n: 'L.top(%s)' % F(z)))
    t = ['u0', 't1', 't2', 't3', 't4']
    emit_unit(out, 'fix', t, [27] * 5, b_fix, record=[('t', t)], mirror_lhs='L.fix(%s)' % F(t), mirror_ty='L.F')
    emit_unit(out, 'key', r, [26] * 5, b_key, record=[('r', r)], mirror_lhs='L.key(%s)' % F(r), mirror_ty='L.K')
    x = ['x%d' % i for i in range(16)] + ['pb']
    emit_unit(out, 'load', x, [8] * 16 + [1], b_load, mirror_lhs='L.load(%s)' % ', '.join(x), mirror_ty='L.F')
    out.append(COMPOSITE)
    return '\n'.join(out)


COMPOSITE = '''# ---- composite functions ----

def ok_carry(z: L.F) -> Bool:
  Bool.and(ok_top(z), ok_fix(L.top(z)))

def carry_mirror(z: L.F) -> {L.carry(z) == L.fix(L.top(z)) : L.F}:
  {==}

def carry_ok(z: L.F, +hz: {B.lim(47n, z) == True{} : Bool}) -> {ok_carry(z) == True{} : Bool}:
  LG.and_intro(ok_top(z), ok_fix(L.top(z)), top_ok_r(z, hz), fix_ok_r(L.top(z), top_fit_r(z, hz)))

def ok_fin(h: L.F, s: L.F) -> Bool:
  Bool.and(ok_top(h), ok_frz(L.top(h), s))

def fin_mirror(h: L.F, s: L.F) -> {L.fin(h, s) == L.frz(L.top(h), s) : List<&2, U32>}:
  {==}

# the final reduction of an accumulator of 27-bit limbs, s of 26-bit limbs
def fin_ok(h: L.F, s: L.F, +hh: {B.lim(27n, h) == True{} : Bool}, +hs: {B.lim(26n, s) == True{} : Bool}) -> {ok_fin(h, s) == True{} : Bool}:
  +h47 = lim_mono(27n, 47n, {==}, h, hh)
  LG.and_intro(ok_top(h), ok_frz(L.top(h), s), top_ok_r(h, h47), frz_ok_r(L.top(h), s, top_fit_r(h, h47), hs))

# one block: h + m, the two products, their combination, the carry pass
def ok_block(k: L.K, h: L.F, m: L.F) -> Bool:
  match k h m:
    case L.K{+e0, +e1, +e2, +e3, +e4, +f1, +f2, +f3, +f4, +o0, +o1, +o2, +o3, +o4, +g1, +g2, +g3, +g4} L.F{+h0, +h1, +h2, +h3, +h4} L.F{+m0, +m1, +m2, +m3, +m4}:
      +a0 = Nat.add(h0, m0)
      +a1 = Nat.add(h1, m1)
      +a2 = Nat.add(h2, m2)
      +a3 = Nat.add(h3, m3)
      +a4 = Nat.add(h4, m4)
      +dd = L.mul(a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, f1, f2, f3, f4)
      +oo = L.mul(a0, a1, a2, a3, a4, o0, o1, o2, o3, o4, g1, g2, g3, g4)
      Bool.and(C.fits(48n, a0), Bool.and(C.fits(48n, a1), Bool.and(C.fits(48n, a2), Bool.and(C.fits(48n, a3), Bool.and(C.fits(48n, a4), Bool.and(ok_mul(a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, f1, f2, f3, f4), Bool.and(ok_mul(a0, a1, a2, a3, a4, o0, o1, o2, o3, o4, g1, g2, g3, g4), Bool.and(ok_comb(dd, oo), ok_carry(L.comb(dd, oo))))))))))

def block_mirror(+e0: Nat, +e1: Nat, +e2: Nat, +e3: Nat, +e4: Nat, +f1: Nat, +f2: Nat, +f3: Nat, +f4: Nat, +o0: Nat, +o1: Nat, +o2: Nat, +o3: Nat, +o4: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat, +h0: Nat, +h1: Nat, +h2: Nat, +h3: Nat, +h4: Nat, +m0: Nat, +m1: Nat, +m2: Nat, +m3: Nat, +m4: Nat) -> {L.block(L.K{e0, e1, e2, e3, e4, f1, f2, f3, f4, o0, o1, o2, o3, o4, g1, g2, g3, g4}, L.F{h0, h1, h2, h3, h4}, L.F{m0, m1, m2, m3, m4}) == L.carry(L.comb(L.mul(Nat.add(h0, m0), Nat.add(h1, m1), Nat.add(h2, m2), Nat.add(h3, m3), Nat.add(h4, m4), e0, e1, e2, e3, e4, f1, f2, f3, f4), L.mul(Nat.add(h0, m0), Nat.add(h1, m1), Nat.add(h2, m2), Nat.add(h3, m3), Nat.add(h4, m4), o0, o1, o2, o3, o4, g1, g2, g3, g4))) : L.F}:
  {==}

# a block with the key of r (26-bit limbs), h of 27-bit limbs, m of 26
def block_ok(+r0: Nat, +r1: Nat, +r2: Nat, +r3: Nat, +r4: Nat, +hr0: {C.fits(26n, r0) == True{} : Bool}, +hr1: {C.fits(26n, r1) == True{} : Bool}, +hr2: {C.fits(26n, r2) == True{} : Bool}, +hr3: {C.fits(26n, r3) == True{} : Bool}, +hr4: {C.fits(26n, r4) == True{} : Bool}, h: L.F, m: L.F, +hh: {B.lim(27n, h) == True{} : Bool}, +hm: {B.lim(26n, m) == True{} : Bool}) -> {ok_block(L.key(L.F{r0, r1, r2, r3, r4}), h, m) == True{} : Bool}:
  match h m:
    case L.F{+h0, +h1, +h2, +h3, +h4} L.F{+m0, +m1, +m2, +m3, +m4}:
BLOCK_BODY
'''


def block_body():
    L_ = []
    ind = '      '
    for i in range(5):
        L_.append('+a%d = Nat.add(h%d, m%d)' % (i, i, i))
        L_.append('+pa%d = B.fa(27n, 26n, h%d, m%d, {==}, B.g%d(27n, h0, h1, h2, h3, h4, hh), B.g%d(26n, m0, m1, m2, m3, m4, hm))' % (i, i, i, i, i))
    for i in range(5):
        L_.append('+e%d = Nat.mod(r%d, 8192n)' % (i, i))
        L_.append('+pe%d = K.fmb(r%d)' % (i, i))
        L_.append('+o%d = Nat.div(r%d, 8192n)' % (i, i))
        L_.append('+po%d = K.fdb(13n, r%d, hr%d)' % (i, i, i))
    for i in range(1, 5):
        L_.append('+f%d = Nat.mul(e%d, 5n)' % (i, i))
        L_.append('+pf%d = B.f5(13n, e%d, pe%d)' % (i, i, i))
        L_.append('+g%d = Nat.mul(o%d, 5n)' % (i, i))
        L_.append('+pg%d = B.f5(13n, o%d, po%d)' % (i, i, i))
    A_ = ', '.join('a%d' % i for i in range(5))
    E_ = ', '.join('e%d' % i for i in range(5))
    O_ = ', '.join('o%d' % i for i in range(5))
    Fs = ', '.join('f%d' % i for i in range(1, 5))
    Gs = ', '.join('g%d' % i for i in range(1, 5))
    PA = ', '.join('pa%d' % i for i in range(5))
    PE = ', '.join('pe%d' % i for i in range(5))
    PO = ', '.join('po%d' % i for i in range(5))
    PF = ', '.join('pf%d' % i for i in range(1, 5))
    PG = ', '.join('pg%d' % i for i in range(1, 5))
    L_.append('+dd = L.mul(%s, %s, %s)' % (A_, E_, Fs))
    L_.append('+oo = L.mul(%s, %s, %s)' % (A_, O_, Gs))
    L_.append('+hd = mul_col(28n, 13n, %s, %s, %s, %s)' % (A_, E_, PA, PE))
    L_.append('+ho = mul_col(28n, 13n, %s, %s, %s, %s)' % (A_, O_, PA, PO))
    atoms = [('C.fits(48n, a%d)' % i, 'B.fm(28n, 48n, a%d, {==}, pa%d)' % (i, i)) for i in range(5)]
    atoms.append(('ok_mul(%s, %s, %s)' % (A_, E_, Fs), 'mul_ok(%s, %s, %s, %s, %s, %s)' % (A_, E_, Fs, PA, PE, PF)))
    atoms.append(('ok_mul(%s, %s, %s)' % (A_, O_, Gs), 'mul_ok(%s, %s, %s, %s, %s, %s)' % (A_, O_, Gs, PA, PO, PG)))
    atoms.append(('ok_comb(dd, oo)', 'comb_ok_r(dd, oo, hd, ho)'))
    atoms.append(('ok_carry(L.comb(dd, oo))', 'carry_ok(L.comb(dd, oo), comb_fit_r(dd, oo, hd, ho))'))
    L_ += conj_lines(atoms)
    return '\n'.join(ind + l for l in L_)


def conj_lines(atoms, tag=''):
    fs = [a[0] for a in atoms]
    n = len(fs)
    L_ = ['+c%s%d = %s' % (tag, n - 1, fs[-1])]
    for i in range(n - 2, -1, -1):
        L_.append('+c%s%d = Bool.and(%s, c%s%d)' % (tag, i, fs[i], tag, i + 1))
    L_.append('+q%s%d = %s' % (tag, n - 1, atoms[-1][1]))
    for i in range(n - 2, -1, -1):
        L_.append('+q%s%d = LG.and_intro(%s, c%s%d, %s, q%s%d)' % (tag, i, fs[i], tag, i + 1, atoms[i][1], tag, i + 1))
    L_.append('q%s0' % tag)
    return L_


def conj_expr(fs):
    e = fs[-1]
    for f in reversed(fs[:-1]):
        e = 'Bool.and(%s, %s)' % (f, e)
    return e


# ---------------------------------------------------------------- safe.bend

def mac_blocks():
    src = open(MAC_SRC).read()

    def cut(start, end):
        i = src.index(start)
        j = src.index(end, i)
        return src[i:j].rstrip() + '\n'
    return [
        cut('def block_inv_k(', '\n# ---- lists'),
        cut('def hd_fit(', '\nlaw take_prefix'),
        cut('def pb_fit(', '\n# ---- the accumulator'),
        cut('law gen_inv:', '\nlaw abs_val:'),
        cut('law abs_inv:', '\n# ---- the tag'),
    ]


def bytes_of(ks):
    return ['L.byte(%s)' % k for k in ks]


CLAMP = [255, 255, 255, 15, 252, 255, 255, 15, 252, 255, 255, 15, 252, 255, 255, 15]


def rbytes(ks):
    return ['L.byte(U32.and(%s, %d))' % (k, c) for k, c in zip(ks, CLAMP)]


def nest(depth_fn, leaf_fn, n, var='x', tl='t', ind='  ', head_var='msg'):
    """16-cell nesting: match msg / t_i; depth_fn(j, cells) for Nil at depth j
    (cells x0..x_j), leaf_fn(cells, rest) at the full pattern"""
    L_ = []
    L_.append(ind + 'match %s:' % head_var)
    L_.append(ind + '  case Nil{}: NILCASE')
    cur = ind + '  '
    prev = None
    for j in range(n):
        L_.append(cur + 'case +%s%d <> +%s:' % (var, j, ('%s%d' % (tl, j)) if j < n - 1 else 'rest'))
        if j < n - 1:
            L_.append(cur + '  match %s%d:' % (tl, j))
            L_.append(cur + '    case Nil{}:')
            L_.append(cur + '      ' + depth_fn(j, ['%s%d' % (var, i) for i in range(j + 1)]))
            cur = cur + '    '
        else:
            for l in leaf_fn(['%s%d' % (var, i) for i in range(n)], 'rest'):
                L_.append(cur + '  ' + l)
    return L_


def lst(cells):
    return ' <> '.join(cells + ['Nil{}'])


KP = 'one, h1, r0, r1, r2, r3, r4, kk, hk, hr0, hr1, hr2, hr3, hr4'
KSIG = ('+one: Nat, +h1: {one == 1n : Nat}, +r0: Nat, +r1: Nat, +r2: Nat, +r3: Nat, +r4: Nat, +kk: L.K, +hk: {kk == L.key(L.F{r0, r1, r2, r3, r4}) : L.K}, '
        '+hr0: {C.fits(26n, r0) == True{} : Bool}, +hr1: {C.fits(26n, r1) == True{} : Bool}, +hr2: {C.fits(26n, r2) == True{} : Bool}, +hr3: {C.fits(26n, r3) == True{} : Bool}, +hr4: {C.fits(26n, r4) == True{} : Bool}')
HRS = 'hr0, hr1, hr2, hr3, hr4'


def hd_chain(ys):
    xs = [ys]
    for i in range(16):
        xs.append('P.tl(%s)' % xs[-1])
    return xs  # xs[i] = tl^i(ys)


def full_blk(cells, ptag):
    """lets and proofs for a full 16-byte block of cells: m, load_ok, block_ok, load_fit"""
    bs = bytes_of(cells)
    m = 'L.load(%s, pone)' % ', '.join(bs)
    pbh = 'LG.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, pone, Equal.sym(Nat, pone, 1n, hp), {==})'
    bfs = ', '.join('B.byte_fit(%s)' % c for c in cells)
    lf = 'B.load_fit(%s, pone, %s, %s)' % (', '.join(bs), bfs, pbh)
    lo = 'O.load_ok(%s, pone, %s, %s)' % (', '.join(bs), bfs, pbh)
    return m, lf, lo


def gen_safe():
    out = []
    out.append('''import Base
import ../../../spec/lib/common.bend as C
import ../../../src/crypto/poly1305/limbs.bend as L
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../lib/logic.bend as LG
import ./nat.bend as K
import ./bnd.bend as B
import ./sops.bend as O

# Generated by tools/generators/poly1305_safe.py (do not edit).
#
# Every Nat the Poly1305 implementation computes stays below 2^48 (Bend's
# native Nat range), for every key and message: ok_* below mirror the
# implementation's loops and entry points (each checked equal to it by
# {==} where it is not a plain match) and put together the limb functions'
# ok predicates of sops.bend at every call; their proofs carry the 27-bit
# accumulator invariant (bnd.bend's block_inv) from block to block. Not
# counted: message lengths and byte counts (List.length, the AEAD's
# lengths and their le8 bytes), which count list cells in memory.
''')
    out.extend(mac_blocks())
    # block_ok with a key named kk
    out.append('''def block_ok_k(%s, h: L.F, m: L.F, +hh: {B.lim(27n, h) == True{} : Bool}, +hm: {B.lim(26n, m) == True{} : Bool}) -> {O.ok_block(kk, h, m) == True{} : Bool}:
  LG.subst(L.K, z => {O.ok_block(z, h, m) == True{} : Bool}, L.key(L.F{r0, r1, r2, r3, r4}), kk, Equal.sym(L.K, kk, L.key(L.F{r0, r1, r2, r3, r4}), hk), O.block_ok(r0, r1, r2, r3, r4, hr0, hr1, hr2, hr3, hr4, h, m, hh, hm))
''' % KSIG)
    # load17
    ys = hd_chain('ys')
    out.append('''# the 17 bytes of a last block (16 of them and the 0x01 byte)
def ok_load17(+ys: List<&2, U32>) -> Bool:
%s
  O.ok_load(%s)

def load17_mirror(+ys: List<&2, U32>) -> {P.load17(ys) == L.load(%s) : L.F}:
  {==}
''' % ('\n'.join('  +y%d = P.tl(%s)' % (i, 'ys' if i == 1 else 'y%d' % (i - 1)) for i in range(1, 16)),
       ', '.join(['P.hd(ys)'] + ['P.hd(y%d)' % i for i in range(1, 16)] + ['P.hd(P.tl(y15))']),
       ', '.join('P.hd(%s)' % y for y in ys)))
    # ok_gen
    out.append('''# absorb_gen (the RFC loop, run on a last short block)
def ok_gen(fuel: Nat, +msg: List<&2, U32>, +k: L.K, h: L.F) -> Bool:
  match fuel msg:
    case 0n _: True{}
    case 1n+f Nil{}: True{}
    case 1n+f +x <> +rest:
      +ys = List.append(&2, U32, P.take(16n, x <> rest), [1])
      +m = P.load17(ys)
      Bool.and(ok_load17(ys), Bool.and(O.ok_block(k, h, m), ok_gen(f, P.skip(16n, x <> rest), k, L.block(k, h, m))))
''')
    hds = ', '.join('P.hd(%s)' % y for y in ys)
    hdf = ', '.join('hd_fit(%s)' % y for y in ys[:16])
    out.append('''def gen_ok(%s, fuel: Nat, +msg: List<&2, U32>, h: L.F, +hh: {B.lim(27n, h) == True{} : Bool}) -> {ok_gen(fuel, msg, kk, h) == True{} : Bool}:
  match fuel msg:
    case 0n _: {==}
    case 1n+f Nil{}: {==}
    case 1n+f +x <> +rest:
      +ys = List.append(&2, U32, P.take(16n, x <> rest), [1])
      +m = P.load17(ys)
      +hm = B.load_fit(%s, %s, pb_fit(x <> rest))
      +q1 = O.load_ok(%s, %s, pb_fit(x <> rest))
      +q2 = block_ok_k(%s, h, m, hh, hm)
      +q3 = gen_ok(%s, f, P.skip(16n, x <> rest), L.block(kk, h, m), block_inv_k(one, h1, r0, r1, r2, r3, r4, %s, kk, hk, h, m, hh, hm))
      LG.and_intro(ok_load17(ys), Bool.and(O.ok_block(kk, h, m), ok_gen(f, P.skip(16n, x <> rest), kk, L.block(kk, h, m))), q1, LG.and_intro(O.ok_block(kk, h, m), ok_gen(f, P.skip(16n, x <> rest), kk, L.block(kk, h, m)), q2, q3))
''' % (KSIG, hds, hdf, hds, hdf, KP, KP, HRS))
    # ok_abs
    X16 = ['x%d' % i for i in range(16)]
    pat = ' <> '.join(X16) + ' <> rest'
    bl = ', '.join(bytes_of(X16))
    out.append('''# absorb (16 bytes per step, a short last block through absorb_gen)
def ok_abs(+pone: Nat, msg: List<&2, U32>, +k: L.K, h: L.F) -> Bool:
  match msg:
    case Nil{}: True{}
    case %s:
      +m = L.load(%s, pone)
      Bool.and(O.ok_load(%s, pone), Bool.and(O.ok_block(k, h, m), ok_abs(pone, rest, k, L.block(k, h, m))))
    case +x <> +rest: ok_gen(List.length(&2, U32, x <> rest), x <> rest, k, h)
''' % (pat, bl, bl))

    def abs_leaf(cells, rest):
        m, lf, lo = full_blk(cells, '')
        return ['+m = %s' % m,
                '+hm = %s' % lf,
                '+q1 = %s' % lo,
                '+q2 = block_ok_k(%s, h, m, hh, hm)' % KP,
                '+q3 = abs_ok(pone, hp, %s, rest, L.block(kk, h, m), block_inv_k(one, h1, r0, r1, r2, r3, r4, %s, kk, hk, h, m, hh, hm))' % (KP, HRS),
                'LG.and_intro(O.ok_load(%s, pone), Bool.and(O.ok_block(kk, h, m), ok_abs(pone, rest, kk, L.block(kk, h, m))), q1, LG.and_intro(O.ok_block(kk, h, m), ok_abs(pone, rest, kk, L.block(kk, h, m)), q2, q3))' % bl]
    body = nest(lambda j, c: 'gen_ok(%s, List.length(&2, U32, %s), %s, h, hh)' % (KP, lst(c), lst(c)), abs_leaf, 16)
    out.append('def abs_ok(+pone: Nat, +hp: {pone == 1n : Nat}, %s, msg: List<&2, U32>, h: L.F, +hh: {B.lim(27n, h) == True{} : Bool}) -> {ok_abs(pone, msg, kk, h) == True{} : Bool}:' % KSIG)
    out.append('\n'.join(body).replace('NILCASE', '{==}'))
    out.append('')
    # ok_pad and pad_inv
    out.append('''# absorb_pad (the AEAD's padded pieces)
def ok_pad(+pone: Nat, msg: List<&2, U32>, +k: L.K, h: L.F, n: Nat) -> Bool:
  match msg:
    case Nil{}: True{}
    case %s:
      +m = L.load(%s, pone)
      Bool.and(O.ok_load(%s, pone), Bool.and(O.ok_block(k, h, m), ok_pad(pone, rest, k, L.block(k, h, m), Nat.add(n, 16n))))
    case +x <> +rest: ok_abs(pone, List.append(&2, U32, x <> rest, P.pad16(x <> rest)), k, h)

def ah(a: P.A) -> L.F:
  match a:
    case P.A{h, n}: h
''' % (pat, bl, bl))

    def pad_leaf(cells, rest):
        m, lf, lo = full_blk(cells, '')
        return ['+m = %s' % m,
                '+hm = %s' % lf,
                '+q1 = %s' % lo,
                '+q2 = block_ok_k(%s, h, m, hh, hm)' % KP,
                '+q3 = pad_ok(pone, hp, %s, rest, L.block(kk, h, m), Nat.add(n, 16n), block_inv_k(one, h1, r0, r1, r2, r3, r4, %s, kk, hk, h, m, hh, hm))' % (KP, HRS),
                'LG.and_intro(O.ok_load(%s, pone), Bool.and(O.ok_block(kk, h, m), ok_pad(pone, rest, kk, L.block(kk, h, m), Nat.add(n, 16n))), q1, LG.and_intro(O.ok_block(kk, h, m), ok_pad(pone, rest, kk, L.block(kk, h, m), Nat.add(n, 16n)), q2, q3))' % bl]
    body = nest(lambda j, c: 'abs_ok(pone, hp, %s, List.append(&2, U32, %s, P.pad16(%s)), h, hh)' % (KP, lst(c), lst(c)), pad_leaf, 16)
    out.append('def pad_ok(+pone: Nat, +hp: {pone == 1n : Nat}, %s, msg: List<&2, U32>, h: L.F, n: Nat, +hh: {B.lim(27n, h) == True{} : Bool}) -> {ok_pad(pone, msg, kk, h, n) == True{} : Bool}:' % KSIG)
    out.append('\n'.join(body).replace('NILCASE', '{==}'))
    out.append('')

    def inv_leaf(cells, rest):
        m, lf, lo = full_blk(cells, '')
        return ['+m = %s' % m,
                'pad_inv(pone, hp, %s, rest, L.block(kk, h, m), Nat.add(n, 16n), block_inv_k(one, h1, r0, r1, r2, r3, r4, %s, kk, hk, h, m, hh, %s))' % (KP, HRS, lf)]
    body = nest(lambda j, c: 'abs_inv(pone, hp, %s, List.append(&2, U32, %s, P.pad16(%s)), h, hh)' % (KP, lst(c), lst(c)), inv_leaf, 16)
    out.append('def pad_inv(+pone: Nat, +hp: {pone == 1n : Nat}, %s, msg: List<&2, U32>, h: L.F, n: Nat, +hh: {B.lim(27n, h) == True{} : Bool}) -> {B.lim(27n, ah(P.absorb_pad(pone, msg, kk, h, n))) == True{} : Bool}:' % KSIG)
    out.append('\n'.join(body).replace('NILCASE', 'hh'))
    out.append('')

    # ---- the tag
    K = ['k%d' % i for i in range(32)]
    rb = rbytes(K[:16])
    sb = bytes_of(K[16:])
    rl = load_strs(rb, '0n')
    rF = 'L.F{%s}' % ', '.join(rl)
    kparams = ', '.join('+%s: U32' % k for k in K)
    kargs = ', '.join(K)
    rbf = ', '.join('B.byte_fit(U32.and(%s, %d))' % (k, c) for k, c in zip(K[:16], CLAMP))
    sbf = ', '.join('B.byte_fit(%s)' % k for k in K[16:])
    hrl = ', '.join('B.g%d(26n, %s, hl)' % (i, ', '.join(rl)) for i in range(5))
    common = '''  +hl = B.load_fit(%s, 0n, %s, {==})
  +hs = B.load_fit(%s, 0n, %s, {==})
  +ql = O.load_ok(%s, 0n, %s, {==})
  +qs = O.load_ok(%s, 0n, %s, {==})
  +qk = O.key_ok_r(P.r_of(%s), hl)''' % (', '.join(rb), rbf, ', '.join(sb), sbf, ', '.join(rb), rbf, ', '.join(sb), sbf, ', '.join(K[:16]))
    out.append('''# the tag: r and s loaded, the key split, the message absorbed, the final reduction
def ok_tag(+pone: Nat, %s, msg: List<&2, U32>) -> Bool:
  +r = P.r_of(%s)
  +k = L.key(r)
  +s = P.s_of(%s)
  Bool.and(O.ok_load(%s, 0n), Bool.and(O.ok_load(%s, 0n), Bool.and(O.ok_key(r), Bool.and(ok_abs(pone, msg, k, L.zero()), O.ok_fin(P.absorb(pone, msg, k, L.zero()), s)))))

def tag_mirror(+pone: Nat, %s, msg: List<&2, U32>) -> {P.tag(pone, %s, msg) == L.fin(P.absorb(pone, msg, L.key(L.load(%s, 0n)), L.zero()), L.load(%s, 0n)) : List<&2, U32>}:
  {==}

def tag_safe(+pone: Nat, +hp: {pone == 1n : Nat}, +one: Nat, +h1: {one == 1n : Nat}, %s, msg: List<&2, U32>) -> {ok_tag(pone, %s, msg) == True{} : Bool}:
%s
  +kk = L.key(P.r_of(%s))
  +qa = abs_ok(pone, hp, one, h1, %s, kk, {==}, %s, msg, L.zero(), {==})
  +ha = abs_inv(pone, hp, one, h1, %s, kk, {==}, %s, msg, L.zero(), {==})
  +qf = O.fin_ok(P.absorb(pone, msg, kk, L.zero()), P.s_of(%s), ha, hs)
%s
''' % (kparams, ', '.join(K[:16]), ', '.join(K[16:]), ', '.join(rb), ', '.join(sb),
       kparams, kargs, ', '.join(rb), ', '.join(sb),
       kparams, kargs, common, ', '.join(K[:16]),
       ', '.join(rl), hrl, ', '.join(rl), hrl, ', '.join(K[16:]),
       '\n'.join('  ' + l for l in conj_lines([
           ('O.ok_load(%s, 0n)' % ', '.join(rb), 'ql'),
           ('O.ok_load(%s, 0n)' % ', '.join(sb), 'qs'),
           ('O.ok_key(P.r_of(%s))' % ', '.join(K[:16]), 'qk'),
           ('ok_abs(pone, msg, kk, L.zero())', 'qa'),
           ('O.ok_fin(P.absorb(pone, msg, kk, L.zero()), P.s_of(%s))' % ', '.join(K[16:]), 'qf')]))))
    pat32 = ' <> '.join(K) + ' <> rest'
    out.append('''def ok_tag_list(+pone: Nat, key: List<&2, U32>, msg: List<&2, U32>) -> Bool:
  match key:
    case %s:
      ok_tag(pone, %s, msg)
    case _:
      True{}

def ok_mac_w(+pone: Nat, +key: List<&2, U32>, msg: List<&2, U32>) -> Bool:
  ok_tag_list(pone, P.pad(32n, key), msg)

def mac_w_safe(+pone: Nat, +hp: {pone == 1n : Nat}, +key: List<&2, U32>, msg: List<&2, U32>) -> {ok_mac_w(pone, key, msg) == True{} : Bool}:
  tag_safe(pone, hp, 1n, {==}, %s, msg)

# mac(key, msg)
def ok_mac(+key: List<&2, U32>, msg: List<&2, U32>) -> Bool:
  match msg:
    case Nil{}: ok_mac_w(1n, key, [])
    case x <> rest: ok_mac_w(1n, key, x <> rest)
''' % (pat32, kargs, ', '.join(padkey(i) for i in range(32))))
    # poly1305_w
    def pw_leaf(cells, rest):
        return ['match rest:',
                '  case Nil{}: tag_safe(pone, hp, 1n, {==}, %s, msg)' % ', '.join(cells),
                '  case _ <> _: {==}']
    body = nest(lambda j, c: '{==}', pw_leaf, 32, var='k', tl='u', head_var='key')
    out.append('''# poly1305(key, msg): the tag for a 32-byte key
def ok_poly1305_w(+pone: Nat, key: List<&2, U32>, msg: List<&2, U32>) -> Bool:
  match key:
    case %s <> Nil{}:
      ok_tag(pone, %s, msg)
    case _:
      True{}

def poly1305_w_safe(+pone: Nat, +hp: {pone == 1n : Nat}, key: List<&2, U32>, msg: List<&2, U32>) -> {ok_poly1305_w(pone, key, msg) == True{} : Bool}:
%s
''' % (' <> '.join(K), kargs, '\n'.join(body).replace('NILCASE', '{==}')))
    # ---- the AEAD tag
    out.append('''# the AEAD tag: aad and ct absorbed with their padding, then the lengths
def ok_tag_len(+pone: Nat, +k: L.K, s: L.F, la: Nat, a: P.A) -> Bool:
  match a:
    case P.A{h, lc}:
      +ms = List.append(&2, U32, P.le8(8n, la), P.le8(8n, lc))
      Bool.and(ok_abs(pone, ms, k, h), O.ok_fin(P.absorb(pone, ms, k, h), s))

def ok_tag_ct(+pone: Nat, +k: L.K, s: L.F, a: P.A, ct: List<&2, U32>) -> Bool:
  match a:
    case P.A{h, la}: Bool.and(ok_pad(pone, ct, k, h, 0n), ok_tag_len(pone, k, s, la, P.absorb_pad(pone, ct, k, h, 0n)))

def tag_len_safe(+pone: Nat, +hp: {pone == 1n : Nat}, %s, s: L.F, +hs: {B.lim(26n, s) == True{} : Bool}, la: Nat, a: P.A, +ha: {B.lim(27n, ah(a)) == True{} : Bool}) -> {ok_tag_len(pone, kk, s, la, a) == True{} : Bool}:
  match a:
    case P.A{h, lc}:
      +ms = List.append(&2, U32, P.le8(8n, la), P.le8(8n, lc))
      LG.and_intro(ok_abs(pone, ms, kk, h), O.ok_fin(P.absorb(pone, ms, kk, h), s), abs_ok(pone, hp, %s, ms, h, ha), O.fin_ok(P.absorb(pone, ms, kk, h), s, abs_inv(pone, hp, %s, ms, h, ha), hs))

def tag_ct_safe(+pone: Nat, +hp: {pone == 1n : Nat}, %s, s: L.F, +hs: {B.lim(26n, s) == True{} : Bool}, a: P.A, ct: List<&2, U32>, +ha: {B.lim(27n, ah(a)) == True{} : Bool}) -> {ok_tag_ct(pone, kk, s, a, ct) == True{} : Bool}:
  match a:
    case P.A{h, la}:
      LG.and_intro(ok_pad(pone, ct, kk, h, 0n), ok_tag_len(pone, kk, s, la, P.absorb_pad(pone, ct, kk, h, 0n)), pad_ok(pone, hp, %s, ct, h, 0n, ha), tag_len_safe(pone, hp, %s, s, hs, la, P.absorb_pad(pone, ct, kk, h, 0n), pad_inv(pone, hp, %s, ct, h, 0n, ha)))

def ok_tag2(+pone: Nat, %s, aad: List<&2, U32>, ct: List<&2, U32>) -> Bool:
  +r = P.r_of(%s)
  +k = L.key(r)
  +s = P.s_of(%s)
  Bool.and(O.ok_load(%s, 0n), Bool.and(O.ok_load(%s, 0n), Bool.and(O.ok_key(r), Bool.and(ok_pad(pone, aad, k, L.zero(), 0n), ok_tag_ct(pone, k, s, P.absorb_pad(pone, aad, k, L.zero(), 0n), ct)))))

def tag2_mirror(+pone: Nat, %s, aad: List<&2, U32>, ct: List<&2, U32>) -> {P.tag2(pone, %s, aad, ct) == P.tag_ct(pone, L.key(P.r_of(%s)), P.s_of(%s), P.absorb_pad(pone, aad, L.key(P.r_of(%s)), L.zero(), 0n), ct) : List<&2, U32>}:
  {==}

def tag2_safe(+pone: Nat, +hp: {pone == 1n : Nat}, +one: Nat, +h1: {one == 1n : Nat}, %s, aad: List<&2, U32>, ct: List<&2, U32>) -> {ok_tag2(pone, %s, aad, ct) == True{} : Bool}:
%s
  +kk = L.key(P.r_of(%s))
  +qa = pad_ok(pone, hp, one, h1, %s, kk, {==}, %s, aad, L.zero(), 0n, {==})
  +ha = pad_inv(pone, hp, one, h1, %s, kk, {==}, %s, aad, L.zero(), 0n, {==})
  +qc = tag_ct_safe(pone, hp, one, h1, %s, kk, {==}, %s, P.s_of(%s), hs, P.absorb_pad(pone, aad, kk, L.zero(), 0n), ct, ha)
%s
''' % (KSIG, KP, KP, KSIG, KP, KP, KP,
       kparams, ', '.join(K[:16]), ', '.join(K[16:]), ', '.join(rb), ', '.join(sb),
       kparams, kargs, ', '.join(K[:16]), ', '.join(K[16:]), ', '.join(K[:16]),
       kparams, kargs, common, ', '.join(K[:16]),
       ', '.join(rl), hrl, ', '.join(rl), hrl, ', '.join(rl), hrl, ', '.join(K[16:]),
       '\n'.join('  ' + l for l in conj_lines([
           ('O.ok_load(%s, 0n)' % ', '.join(rb), 'ql'),
           ('O.ok_load(%s, 0n)' % ', '.join(sb), 'qs'),
           ('O.ok_key(P.r_of(%s))' % ', '.join(K[:16]), 'qk'),
           ('ok_pad(pone, aad, kk, L.zero(), 0n)', 'qa'),
           ('ok_tag_ct(pone, kk, P.s_of(%s), P.absorb_pad(pone, aad, kk, L.zero(), 0n), ct)' % ', '.join(K[16:]), 'qc')]))))
    out.append('''def ok_tag2_list(+pone: Nat, key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> Bool:
  match key:
    case %s:
      ok_tag2(pone, %s, aad, ct)
    case _:
      True{}

def ok_mac_aead_w(+pone: Nat, +key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> Bool:
  ok_tag2_list(pone, P.pad(32n, key), aad, ct)

def mac_aead_w_safe(+pone: Nat, +hp: {pone == 1n : Nat}, +key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> {ok_mac_aead_w(pone, key, aad, ct) == True{} : Bool}:
  tag2_safe(pone, hp, 1n, {==}, %s, aad, ct)

# mac_aead(key, aad, ct)
def ok_mac_aead(+key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> Bool:
  match aad:
    case Nil{}: ok_mac_aead_w(1n, key, [], ct)
    case x <> rest: ok_mac_aead_w(1n, key, x <> rest, ct)

# ---- the clauses ----

# mac: every Nat computed for any key and message is below 2^48
law safe_mac:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {ok_mac(key, msg) == True{} : Bool}

def safe_mac(key, msg):
  match msg:
    case Nil{}: mac_w_safe(1n, {==}, key, [])
    case x <> rest: mac_w_safe(1n, {==}, key, x <> rest)

# poly1305 (and verify, which computes mac): the same
law safe_poly1305:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {ok_poly1305_w(1n, key, msg) == True{} : Bool}

def safe_poly1305(key, msg):
  poly1305_w_safe(1n, {==}, key, msg)

# mac_aead (the ChaCha20-Poly1305 tag): the same, for any aad and ciphertext
law safe_mac_aead:
  for +key: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {ok_mac_aead(key, aad, ct) == True{} : Bool}

def safe_mac_aead(key, aad, ct):
  match aad:
    case Nil{}: mac_aead_w_safe(1n, {==}, key, [], ct)
    case x <> rest: mac_aead_w_safe(1n, {==}, key, x <> rest, ct)
''' % (pat32, kargs, ', '.join(padkey(i) for i in range(32))))
    return '\n'.join(out)


def padkey(i):
    e = 'key'
    for _ in range(i):
        e = 'P.tl(%s)' % e
    return 'P.kh(%s)' % e


def plus(text):
    """every parameter of a def is marked + (used more than once)"""
    out = []
    for l in text.split('\n'):
        if l.startswith('def ') and ')' in l:
            i = l.index('(')
            l = l[:i] + re.sub(r'([(,]\s*)([a-z_][A-Za-z0-9_]*): ', r'\1+\2: ', l[i:])
        out.append(l)
    return '\n'.join(out)


def main():
    s = gen_sops().replace('BLOCK_BODY', block_body())
    open(os.path.join(OUT, 'sops.bend'), 'w').write(plus(s))
    open(os.path.join(OUT, 'safe.bend'), 'w').write(plus(gen_safe()))
    print('bytes l4 width', BYTES_BITS)


if __name__ == '__main__':
    main()
