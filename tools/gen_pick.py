#!/usr/bin/env python3
"""Write src/crypto/ed25519/pick.bend and proofs/crypto/ed25519/pickb.bend,
pickr.bend.

sel16 selects one of 16 field elements by 16 masks (one of them 1, the
others 0) without a branch: limb j of the result is the sum over i of
mask_i * limb j of element i, each product on the 32-bit multiplier. It is
the list form LS.pick of src/crypto/curve25519/limbs.bend evaluated on
symbolic limbs (as tools/gen_fe.py writes the field operations);
pickb.bend checks that with one evaluation. pickr.bend relates PT.look
(sel16 over a row of 16 prepared points) and a row built by PT.row to the
specification's row, one case per digit.

  python3 tools/gen_pick.py            rewrite both files
  python3 tools/gen_pick.py --check    fail if either is out of date
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'src/crypto/ed25519/pick.bend'
BRIDGE = ROOT / 'proofs/crypto/ed25519/pickb.bend'
REL = ROOT / 'proofs/crypto/ed25519/pickr.bend'
N, W = 16, 15


def generate():
    o = ['''import Base
import ../curve25519/fe.bend as FE

# Selection of one of 16 field elements by masks, without a branch
# (written by tools/gen_pick.py from the list form LS.pick of
# ../curve25519/limbs.bend; do not edit by hand). With mask i equal to 1
# and the others 0, the result is element i: limb j is the sum of
# mask_i * limb j of element i, each product on the 32-bit multiplier
# (limbs are below 2^32).

type M16 is Data:
  M16{%s}
''' % ', '.join('m%d: Nat' % i for i in range(N))]
    o.append('def sel16(mk: M16, %s) -> FE.Fe:' % ', '.join('f%d: FE.Fe' % i for i in range(N)))
    o.append('  match mk %s:' % ' '.join('f%d' % i for i in range(N)))
    o.append('    case M16{%s} %s:' % (', '.join('+m%d' % i for i in range(N)),
                                      ' '.join('FE.Fe{' + ', '.join('x%d_%d' % (i, j) for j in range(W)) + '}' for i in range(N))))
    for i in range(N):
        o.append('      +u%d = U32.from_nat(m%d)' % (i, i))

    def limb(j):
        e = '0n'
        for i in reversed(range(N)):
            e = 'Nat.add(U32.to_nat(U32.mul(U32.from_nat(x%d_%d), u%d)), %s)' % (i, j, i, e)
        return e
    o.append('      FE.Fe{%s}' % ', '.join(limb(j) for j in range(W)))
    return '\n'.join(o) + '\n'


def bridge():
    ms = ', '.join('m%d' % i for i in range(N))
    fs = ', '.join('f%d' % i for i in range(N))
    return '''import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/ed25519/pick.bend as PK

# The straight-line selection is the list form on the limbs: one
# evaluation on symbolic limbs (written by tools/gen_pick.py together
# with src/crypto/ed25519/pick.bend).

def sel16_b(%s, %s) -> {FE.to_list(PK.sel16(PK.M16{%s}, %s)) == LS.pick(15n, [%s], [%s]) : List<&2, Nat>}:
  match %s:
    case %s:
      {==}
''' % (', '.join('+m%d: Nat' % i for i in range(N)), ', '.join('+f%d: FE.Fe' % i for i in range(N)), ms, fs, ms,
       ', '.join('FE.to_list(f%d)' % i for i in range(N)), ' '.join('f%d' % i for i in range(N)),
       ' '.join('FE.Fe{' + ', '.join('x%d_%d' % (i, j) for j in range(W)) + '}' for i in range(N)))


def rel():
    K = range(N)
    fields = ', '.join('+a%d: FE.Fe, +b%d: FE.Fe, +c%d: FE.Fe, +d%d: FE.Fe' % (i, i, i, i) for i in K)
    ss = ', '.join('+s%d: SE.EPt' % i for i in K)
    rs = ', '.join('+r%d: PT2.Rc(one, pp, D, PT.Cp{a%d, b%d, c%d, d%d}, s%d)' % (i, i, i, i, i, i) for i in K)
    row = '[' + ', '.join('PT.Cp{a%d, b%d, c%d, d%d}' % (i, i, i, i) for i in K) + ']'
    srow = '[' + ', '.join('s%d' % i for i in K) + ']'

    def tl(ch):
        return '[' + ', '.join('FE.to_list(%s%d)' % (ch, i) for i in K) + ']'

    def lst(ch):
        return ', '.join('%s%d' % (ch, i) for i in K)
    oks = ', '.join('+ok%s: {PP.okf(one, 15n, %s) == True{} : Bool}' % (ch.upper(), tl(ch)) for ch in 'abcd')
    o = ['''import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/pick.bend as PK
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../fe/rel.bend as RE
import ./prel.bend as PR
import ./pdec.bend as PD
import ./pickp.bend as PP
import ./ptab.bend as PT2
import ./fbspec.bend as FB

# The row lookup of src/crypto/ed25519/point.bend (look: selection by
# masks over 16 prepared points) against the specification's row (written
# by tools/gen_pick.py): entry i of related rows is related, for i < 16;
# and the row PT.row builds is related to the specification's row.

# on the fields of the 16 entries, one case per digit
def look_cs(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +D: Nat, %s, %s, %s, %s, +i: Nat, +hi: {Nat.is_lt(i, 16n) == True{} : Bool}) -> PT2.Rc(one, pp, D, PT.look(i, %s), FB.snth(i, %s)):
  match i:''' % (fields, ss, rs, oks, row, srow)]
    for k in K:
        masks = ', '.join('1n' if j == k else '0n' for j in K)
        o.append('    case %dn:' % k)
        for ch in 'abcd':
            o.append('      +x%s = PK.sel16(PK.M16{%s}, %s)' % (ch, masks, lst(ch)))

        def eq(ch):
            return 'PP.sel_i(one, h1, %s, %s, ok%s, %dn, {==}, %s%d, {==})' % (masks, lst(ch), ch.upper(), k, ch, k)
        args = 'one, pp, D, a%d, b%d, c%d, d%d, s%d, r%d' % (k, k, k, k, k, k)
        o.append('      PT2.mk(one, pp, D, xa, xb, xc, xd, s%d, RE.r_eq(one, pp, xa, a%d, FS.fadd(1n+pp, FB.sy(s%d), FB.sx(s%d)), %s, PT2.cA(%s)), RE.r_eq(one, pp, xb, b%d, FS.fsub(1n+pp, FB.sy(s%d), FB.sx(s%d)), %s, PT2.cB(%s)), RE.r_eq(one, pp, xc, c%d, FS.fmul(1n+pp, FB.st(s%d), FS.fadd(1n+pp, D, D)), %s, PT2.cC(%s)), RE.r_eq(one, pp, xd, d%d, FS.fadd(1n+pp, FB.sz(s%d), FB.sz(s%d)), %s, PT2.cD(%s)))' % (
            k, k, k, k, eq('a'), args, k, k, k, eq('b'), args, k, k, eq('c'), args, k, k, k, eq('d'), args))
    o.append('    case 16n+m:')
    o.append('      Empty.absurd(PT2.Rc(one, pp, D, PT.look(16n+m, %s), FB.snth(16n+m, %s)), N.lt_zero_absurd(m, hi))' % (row, srow))
    es = ', '.join('+e%d: PT.Cp' % i for i in K)
    rs2 = ', '.join('+r%d: PT2.Rc(one, pp, D, e%d, s%d)' % (i, i, i) for i in K)
    erow = '[' + ', '.join('e%d' % i for i in K) + ']'
    o.append('''
# entry i of related rows is related
def look_rc(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +D: Nat, %s, %s, %s, +i: Nat, +hi: {Nat.is_lt(i, 16n) == True{} : Bool}) -> PT2.Rc(one, pp, D, PT.look(i, %s), FB.snth(i, %s)):
  match %s:
    case %s:''' % (es, ss, rs2, erow, srow, ' '.join('e%d' % i for i in K), ' '.join('PT.Cp{+a%d, +b%d, +c%d, +d%d}' % (i, i, i, i) for i in K)))

    def okf(ch, acc, spec):
        return 'PP.okf16(one, %s, %s)' % (lst(ch), ', '.join('RE.o(one, pp, %s%d, %s, PT2.c%s(one, pp, D, a%d, b%d, c%d, d%d, s%d, r%d))' % (ch, i, spec % {'i': i}, acc, i, i, i, i, i, i) for i in K))
    o.append('      look_cs(one, h1, pp, D, %s, %s, %s, %s, %s, %s, %s, i, hi)' % (
        ', '.join('a%d, b%d, c%d, d%d' % (i, i, i, i) for i in K), lst('s'), lst('r'),
        okf('a', 'A', 'FS.fadd(1n+pp, FB.sy(s%(i)d), FB.sx(s%(i)d))'),
        okf('b', 'B', 'FS.fsub(1n+pp, FB.sy(s%(i)d), FB.sx(s%(i)d))'),
        okf('c', 'C', 'FS.fmul(1n+pp, FB.st(s%(i)d), FS.fadd(1n+pp, D, D))'),
        okf('d', 'D', 'FS.fadd(1n+pp, FB.sz(s%(i)d), FB.sz(s%(i)d))')))
    o.append('''
# entry i of the row of a related point is the specification row's entry
def row_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +i: Nat, +hi: {Nat.is_lt(i, 16n) == True{} : Bool}) -> PT2.Rc(one, pp, D, PT.look(i, PT.row(cs, p)), FB.snth(i, FB.srow(1n+pp, D, sp))):
  +m0 = PT.identity()
  +t0 = SE.identity()
  +g0 = PD.identity_rel(one, h1, pp)
  +m1 = p
  +t1 = sp
  +g1 = hp''')
    for k in range(2, N):
        o.append('  +m%d = PT.add(cs, m%d, p)' % (k, k - 1))
        o.append('  +t%d = SE.add(1n+pp, D, t%d, sp)' % (k, k - 1))
        o.append('  +g%d = PR.add_rel(one, h1, pp, hP, cs, hR, D, rd2, m%d, p, t%d, sp, g%d, hp)' % (k, k - 1, k - 1, k - 1))
    o.append('  look_rc(one, h1, pp, D, %s, %s, %s, i, hi)' % (
        ', '.join('PT.cached(cs, m%d)' % i for i in K), ', '.join('t%d' % i for i in K),
        ', '.join('PT2.cached_rel(one, h1, pp, hP, cs, hR, D, rd2, m%d, t%d, g%d)' % (i, i, i) for i in K)))
    return '\n'.join(o) + '\n'


def main():
    text, btext, rtext = generate(), bridge(), rel()
    if '--check' in sys.argv:
        if OUT.read_text() != text or BRIDGE.read_text() != btext or REL.read_text() != rtext:
            print('pick.bend, pickb.bend or pickr.bend is out of date: run python3 tools/gen_pick.py')
            return 1
        return 0
    OUT.write_text(text)
    BRIDGE.write_text(btext)
    REL.write_text(rtext)
    return 0


if __name__ == '__main__':
    sys.exit(main())
