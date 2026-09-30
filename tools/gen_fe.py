#!/usr/bin/env python3
"""Write src/crypto/curve25519/fe.bend.

The straight-line field operations of fe.bend (add, sub, mul, mul_small,
select) are the reference list algorithms of src/crypto/curve25519/limbs.bend
evaluated on 15 symbolic limbs. This script mirrors those definitions on
symbolic terms, so each generated body is, after its lets are substituted,
exactly the normal form the proof checker computes for the reference form
(proofs/crypto/fe/bridge.bend checks each with one evaluation). Every
subterm used twice is let-bound once, so the compiled code computes it once.

  python3 tools/gen_fe.py            rewrite src/crypto/curve25519/fe.bend
  python3 tools/gen_fe.py --check    fail if the file is out of date
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'src/crypto/curve25519/fe.bend'
N = 15


# ---- symbolic terms: ('v', name) | ('lit', text) | (op, args...) ----

def V(n):
    return ('v', n)


def lit(t):
    return ('lit', t)


def op(o, *a):
    return (o,) + a


# mirrors of src/crypto/curve25519/limbs.bend (same argument order)
def addl(xs, ys):
    if not xs:
        return ys
    if not ys:
        return xs
    return [op('Nat.add', xs[0], ys[0])] + addl(xs[1:], ys[1:])


def scal(a, ys):
    return [op('Nat.mul', a, y) for y in ys]


def scal_r(ys, k):
    return [op('Nat.mul', y, k) for y in ys]


def conv(xs, ys):
    if not xs or not ys:
        return []
    return [op('Nat.mul', xs[0], ys[0])] + addl(scal(xs[0], ys[1:]), conv(xs[1:], ys))


def pu(a, b):
    return op('U32.to_nat', op('U32.mul', op('U32.from_nat', a), op('U32.from_nat', b)))


def pm(a, b):
    return op('Nat.add', pu(a, op('Nat.mod', b, lit('512n'))), op('Nat.mul', pu(a, op('Nat.div', b, lit('512n'))), lit('512n')))


def scalp(a, ys):
    return [pm(a, y) for y in ys]


def convp(xs, ys):
    if not xs or not ys:
        return []
    return [pm(xs[0], ys[0])] + addl(scalp(xs[0], ys[1:]), convp(xs[1:], ys))


def dbl(ys):
    return [op('Nat.add', y, y) for y in ys]


def sqp(xs):
    if not xs:
        return []
    if len(xs) == 1:
        return [pm(xs[0], xs[0])]
    x, t0, tt = xs[0], xs[1], xs[2:]
    return [pm(x, x), pm(x, op('Nat.add', t0, t0))] + addl(scalp(x, dbl(tt)), sqp(xs[1:]))


def fold(zs):
    return addl(zs[:15], scal_r(zs[15:], lit('19n')))


def subl(xs, ys, ks):
    return [op('Nat.sub', op('Nat.add', x, k), y) for x, y, k in zip(xs, ys, ks)]


def kp8(R):
    return [op('Nat.sub', op('Nat.mul', R, lit('8n')), lit('152n'))] + \
        [op('Nat.sub', op('Nat.mul', R, lit('8n')), lit('8n'))] * 14


def sel(s, xs, ys):
    return [op('Nat.add', op('Nat.mul', x, op('Nat.sub', lit('1n'), s)), op('Nat.mul', y, s)) for x, y in zip(xs, ys)]


def carry(R, xs, c):
    if not xs:
        return [], c
    s = op('Nat.add', xs[0], c)
    rest, out = carry(R, xs[1:], op('Nat.div', s, R))
    return [op('Nat.mod', s, R)] + rest, out


def carry0(R, xs):
    if not xs:
        return [], lit('0n')
    rest, out = carry(R, xs[1:], op('Nat.div', xs[0], R))
    return [op('Nat.mod', xs[0], R)] + rest, out


def pass_(R, xs):
    ls, c = carry0(R, xs)
    t = op('Nat.add', ls[0], op('Nat.mul', c, lit('19n')))
    return [op('Nat.mod', t, R), op('Nat.add', ls[1], op('Nat.div', t, R))] + ls[2:]


# ---- emission ----

def show(t, names):
    if t in names:
        return names[t]
    if t[0] in ('v', 'lit'):
        return t[1]
    return '%s(%s)' % (t[0], ', '.join(show(a, names) for a in t[1:]))


def emit(outs, pre):
    """(let lines, result expressions): every subterm used twice is bound once"""
    cnt = {}

    def count(t):
        cnt[t] = cnt.get(t, 0) + 1
        if cnt[t] == 1 and t[0] not in ('v', 'lit'):
            for a in t[1:]:
                count(a)
    for o in outs:
        count(o)
    names, lines = {}, []

    def visit(t):
        if t[0] in ('v', 'lit') or t in names:
            return
        for a in t[1:]:
            visit(a)
        if cnt[t] > 1:
            nm = '%s%d' % (pre, len(names))
            lines.append('+%s = %s' % (nm, show(t, names)))
            names[t] = nm
    for o in outs:
        visit(o)
    return lines, [show(o, names) for o in outs]


A = [V('a%d' % i) for i in range(N)]
B = [V('b%d' % i) for i in range(N)]
R = V('R')


def pat(xs, plus=True):
    return 'Fe{' + ', '.join(('+' if plus else '') + x[1] for x in xs) + '}'


def flat(name, sig, match, outs, doc, pre=None):
    lines, res = emit(outs, 'w')
    body = ['# ' + d for d in doc]
    body.append('def %s -> Fe:' % sig)
    ind = '  '
    if match:
        body.append(ind + 'match %s:' % ' '.join(m[0] for m in match))
        body.append(ind + '  case %s:' % ' '.join(m[1] for m in match))
        ind = ind + '    '
    if pre:
        for p in pre:
            body.append(ind + p)
    for l in lines:
        body.append(ind + l)
    body.append(ind + 'Fe{' + ', '.join(res) + '}')
    return '\n'.join(body) + '\n'


HEADER = '''import Base
import ./limbs.bend as LS

# GF(p), p = 2^255 - 19, for X25519 and Ed25519: 15 limbs of 17 bits,
# value(x) = l0 + 2^17 l1 + ... + 2^238 l14 (spec/crypto/curve25519/fe.bend).
# The limbs are Nat: the native backend keeps a Nat below 2^48 in one
# machine word, and every intermediate here stays below 2^47 (proved: an
# element is "ok" when its limbs are below 2^19; the schoolbook product of
# two ok elements has columns below 15 * 2^38, the fold by 19 keeps them
# below 2^47, and a carry pass brings them back to ok). This is the
# unsaturated-limb field of Fiat-Crypto (Erbsen et al. 2019) and HACL*'s
# Field51, with 17-bit limbs so that products and sums fit the 48-bit Nat.
#
# add, sub, mul, mul_small and select are straight-line code, written by
# tools/gen_fe.py from the list algorithms of limbs.bend (do not edit them
# by hand; rerun the script). Every operation takes the radix R = 2^17,
# which the callers compute once from their symbolic one (radix(one)), so
# the proofs never meet a closed 2^17.
#
# No operation branches on a limb: selection is arithmetic, the exponents
# of inv and pow_p58 are public, and freeze's subtraction is a selection.
# Bend has no timing model, so constant time is by construction, not
# proved.

type Fe is Data:
  Fe{l0: Nat, l1: Nat, l2: Nat, l3: Nat, l4: Nat, l5: Nat, l6: Nat, l7: Nat, l8: Nat, l9: Nat, l10: Nat, l11: Nat, l12: Nat, l13: Nat, l14: Nat}

def to_list(x: Fe) -> List<&2, Nat>:
  match x:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14]

# the first 15 limbs of a list (missing limbs are 0)
def lhd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      x

def ltl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      xt

def of_list(xs: List<&2, Nat>) -> Fe:
  match xs:
    case Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, t}}}}}}}}}}}}}}}:
      Fe{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14}
    case _:
      Fe{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# 2^n x
def pow2(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      Nat.double(pow2(m, x))

# the radix 2^17, from the symbolic one (1n at run time)
def radix(+one: Nat) -> Nat:
  pow2(17n, one)

# ---- constants ----

def zero() -> Fe:
  Fe{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def one() -> Fe:
  Fe{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# a constant k < 2^17
def small(k: Nat) -> Fe:
  Fe{k, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# ---- straight-line operations (tools/gen_fe.py) ----
'''

FOOTER = '''
def neg(+R: Nat, a: Fe) -> Fe:
  sub(R, zero(), a)

# ---- powers (public exponents) ----
#
# The loops take the base x first and inspect it before their counter, so
# the proof checker never unfolds a fixed-count loop over an unknown base.

# y^(2^n): n squarings. g is the chain's base, passed unchanged and
# inspected first, so the proof checker never unfolds the loop over an
# unknown base.
def sqn(+R: Nat, +g: Fe, n: Nat, y: Fe) -> Fe:
  match g:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      match n:
        case 0n:
          y
        case 1n+m:
          sqn(R, g, m, sq(R, y))

# y^(2^m) z: with y = x^(2^n - 1) and z = x^(2^m - 1), x^(2^(n + m) - 1)
def cat(+R: Nat, +g: Fe, y: Fe, z: Fe, m: Nat) -> Fe:
  mul(R, sqn(R, g, m, y), z)

# x^(2^250 - 1): the addition chain of ref10's fe_invert (249 squarings,
# 10 multiplications)
def p250(+R: Nat, +x: Fe) -> Fe:
  +z2 = cat(R, x, x, x, 1n)
  +z4 = cat(R, x, z2, z2, 2n)
  +z5 = cat(R, x, z4, x, 1n)
  +z10 = cat(R, x, z5, z5, 5n)
  +z20 = cat(R, x, z10, z10, 10n)
  +z40 = cat(R, x, z20, z20, 20n)
  +z50 = cat(R, x, z40, z10, 10n)
  +z100 = cat(R, x, z50, z50, 50n)
  +z200 = cat(R, x, z100, z100, 100n)
  cat(R, x, z200, z50, 50n)

# one bit of a public exponent, most significant first: acc^2 (* x)
def pow_bit(+R: Nat, b: Bool, +x: Fe, acc: Fe) -> Fe:
  match b:
    case True{}:
      mul(R, sq(R, acc), x)
    case False{}:
      sq(R, acc)

def pow_bits(+R: Nat, +x: Fe, bs: List<&2, Bool>, acc: Fe) -> Fe:
  match x:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      match bs:
        case Nil{}:
          acc
        case Con{b, bt}:
          pow_bits(R, x, bt, pow_bit(R, b, x, acc))

# x^(p - 2) = x^(2^255 - 21): 250 one bits, then 0 1 0 1 1
def inv(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}, False{}, True{}, True{}], p250(R, x))

# x^((p - 5) / 8) = x^(2^252 - 3): 250 one bits, then 0 1
def pow_p58(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}], p250(R, x))

# ---- canonical form and bytes (list form, limbs.bend) ----

# the canonical representative: limbs below R, value below p
def freeze(+R: Nat, x: Fe) -> Fe:
  of_list(LS.freeze_l(R, to_list(x)))

# the 32-byte little-endian encoding of the canonical representative
def to_bytes(+R: Nat, x: Fe) -> List<&2, U32>:
  LS.to_bytes_l(LS.freeze_l(R, to_list(x)))

# 32 bytes to an element, bit 255 ignored (RFC 7748 decodeUCoordinate)
def of_bytes(bs: List<&2, U32>) -> Fe:
  of_list(LS.of_bytes_l(bs))

# x == 0 in the field: every limb of the canonical form is 0
def is_zero(+R: Nat, x: Fe) -> Bool:
  Nat.is_eq(LS.sum(LS.freeze_l(R, to_list(x)), 0n), 0n)

# a == b in the field
def eq(+R: Nat, a: Fe, b: Fe) -> Bool:
  is_zero(R, sub(R, a, b))

# the parity of the canonical representative (RFC 8032 x_0)
def parity(+R: Nat, x: Fe) -> U32:
  U32.from_nat(Nat.mod(LS.head(LS.freeze_l(R, to_list(x))), 2n))
'''


def generate():
    parts = [HEADER]
    parts.append(flat('add', 'add(+R: Nat, a: Fe, b: Fe)', [('a', pat(A)), ('b', pat(B))],
                      pass_(R, addl(A, B)), ['a + b: LS.add_l']))
    parts.append(flat('sub', 'sub(+R: Nat, a: Fe, b: Fe)', [('a', pat(A)), ('b', pat(B))],
                      pass_(R, subl(A, B, kp8(R))), ['a + 8 p - b: LS.sub_l']))
    parts.append(flat('mul', 'mul(+R: Nat, a: Fe, b: Fe)', [('a', pat(A)), ('b', pat(B))],
                      pass_(R, fold(convp(A, B))), ['a b: LS.mul_l']))
    parts.append(flat('sq', 'sq(+R: Nat, a: Fe)', [('a', pat(A))],
                      pass_(R, fold(sqp(A))), ['a^2, each cross product once: LS.sq_l']))
    K = V('k')
    parts.append(flat('mul_small', 'mul_small(+R: Nat, a: Fe, +k: Nat)', [('a', pat(A))],
                      pass_(R, scal_r(A, K)), ['a k for k < 2^17: LS.mul_small_l']))
    S = V('sn')
    parts.append(flat('select', 'select(+s: U32, a: Fe, b: Fe)', [('a', pat(A)), ('b', pat(B))],
                      sel(S, A, B), ['s == 0: a; s == 1: b (LS.sel on U32.to_nat(s))'], pre=['+sn = U32.to_nat(s)']))
    return '\n'.join(parts) + FOOTER


BRIDGE = ROOT / 'proofs/crypto/fe/bridge.bend'


def bridge():
    fa = 'FE.Fe{' + ', '.join('a%d' % i for i in range(N)) + '}'
    fb = 'FE.Fe{' + ', '.join('b%d' % i for i in range(N)) + '}'
    L = 'List<&2, Nat>'
    out = ['''import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ./pass.bend as PS

# Each straight-line operation of src/crypto/curve25519/fe.bend is its
# reference list algorithm (src/crypto/curve25519/limbs.bend) on the limbs:
# one evaluation per operation, on symbolic limbs (written by
# tools/gen_fe.py together with fe.bend).
''']
    for name, args, sig, ref, both in [
            ('add', 'R, a, b', '+R: Nat, +a: FE.Fe, +b: FE.Fe', 'LS.add_l(R, FE.to_list(a), FE.to_list(b))', True),
            ('sub', 'R, a, b', '+R: Nat, +a: FE.Fe, +b: FE.Fe', 'LS.sub_l(R, FE.to_list(a), FE.to_list(b))', True),
            ('mul', 'R, a, b', '+R: Nat, +a: FE.Fe, +b: FE.Fe', 'LS.mul_l(R, FE.to_list(a), FE.to_list(b))', True),
            ('sq', 'R, a', '+R: Nat, +a: FE.Fe', 'LS.sq_l(R, FE.to_list(a))', False),
            ('mul_small', 'R, a, k', '+R: Nat, +a: FE.Fe, +k: Nat', 'LS.mul_small_l(R, FE.to_list(a), k)', False),
            ('select', 's, a, b', '+s: U32, +a: FE.Fe, +b: FE.Fe', 'LS.sel(U32.to_nat(s), FE.to_list(a), FE.to_list(b))', True)]:
        m = 'a b' if both else 'a'
        c = (fa + ' ' + fb) if both else fa
        out.append('def %s_b(%s) -> {FE.to_list(FE.%s(%s)) == %s : %s}:\n  match %s:\n    case %s:\n      {==}\n' % (
            name, sig, name, args, ref, L, m, c))
    out.append(to_of())
    return '\n'.join(out)


def to_of():
    """to_list(of_list(zs)) == zs for 15 limbs, by 16 nested matches"""
    L = 'List<&2, Nat>'
    lines = ['# of_list inverts to_list on 15 limbs',
             'def to_of(+zs: %s, +hl: {PS.ln(zs) == 15n : Nat}) -> {FE.to_list(FE.of_list(zs)) == zs : %s}:' % (L, L)]

    def lst(k, tail):
        e = tail
        for i in reversed(range(k)):
            e = 'Con{x%d, %s}' % (i, e)
        return e

    def absurd(k, tail):
        cur = lst(k, tail)
        goal = '{FE.to_list(FE.of_list(%s)) == %s : %s}' % (cur, cur, L)
        return 'Empty.absurd(%s, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(%s), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(%s), z) == True{} : Bool}, PS.ln(%s), 15n, hl, N.is_eq_refl(PS.ln(%s))))))' % (goal, cur, cur, cur, cur)
    ind = '  '
    var = 'zs'
    for k in range(16):
        lines.append(ind + 'match %s:' % var)
        lines.append(ind + '  case Nil{}:')
        if k == 15:
            lines.append(ind + '    {==}')
        else:
            lines.append(ind + '    ' + absurd(k, 'Nil{}'))
        nv = 'z%d' % (k + 1)
        lines.append(ind + '  case Con{+x%d, +%s}:' % (k, nv))
        if k == 15:
            lines.append(ind + '    ' + absurd(16, nv))
            break
        ind += '    '
        var = nv
    return '\n'.join(lines) + '\n'


def main():
    text = generate()
    btext = bridge()
    if '--check' in sys.argv:
        if OUT.read_text() != text or BRIDGE.read_text() != btext:
            print('fe.bend or bridge.bend is out of date: run python3 tools/gen_fe.py')
            return 1
        return 0
    OUT.write_text(text)
    BRIDGE.parent.mkdir(parents=True, exist_ok=True)
    BRIDGE.write_text(btext)
    return 0


if __name__ == '__main__':
    sys.exit(main())
