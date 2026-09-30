#!/usr/bin/env python3
"""Writes the group-law clauses of secp256k1:

  proofs/crypto/secp256k1/group/glawp.bend   each clause on FS.prime(one), with the two
                                             facts about p as hypotheses hp, hc (light:
                                             what other proofs import)
  proofs/crypto/secp256k1/laws_group.bend    the public clauses, unconditional
  proofs/crypto/secp256k1/proof_group.bend   their root: glawp applied to the
                                             certificates group/certa.bend, group/certd.bend

  python3 tools/generators/secp256k1_group/gen_laws.py
"""
import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', '..', '..', 'proofs', 'crypto', 'secp256k1')
P = 'FS.prime(one)'


def V(p, a):
    return '{GS.valid(%s, %s) == True{} : Bool}' % (p, a)


def E(p, a, b):
    return '{GS.equiv(%s, %s, %s) == True{} : Bool}' % (p, a, b)


def A(p, a, b):
    return 'CS.padd(%s, %s, %s)' % (p, a, b)


def S(p, k, a):
    return 'GS.smul(%s, %s, %s)' % (p, k, a)


SP = 'CS.SPoint'
# (law, comment, variables, hypotheses (name, type of p), conclusion of p, proof on 1 + pm with $h for a moved hypothesis)
LAWS = [
    ('Group.closed', 'the sum of two points of the group is a point of the group', [('a', SP), ('b', SP)], [('va', lambda p: V(p, 'a')), ('vb', lambda p: V(p, 'b'))], lambda p: V(p, A(p, 'a', 'b')), 'G1.v_add(FPA, a, b, $va, $vb)'),
    ('Group.infinity', '(0 : 1 : 0) is a point of the group', [], [], lambda p: V(p, 'CS.infinity()'), 'G2.v_inf(PM1, H21)'),
    ('Group.neg_closed', '-A is a point of the group', [('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: V(p, 'GS.neg(%s, a)' % p), 'G2.v_neg(PM1, a, $va)'),
    ('Group.commutative', 'A + B = B + A, as triples', [('a', SP), ('b', SP)], [], lambda p: '{%s == %s : CS.SPoint}' % (A(p, 'a', 'b'), A(p, 'b', 'a')), 'G1.add_comm(PM1, a, b)'),
    ('Group.associative', '(A + B) + C and A + (B + C) are the same projective point', [('a', SP), ('b', SP), ('c', SP)], [('va', lambda p: V(p, 'a')), ('vb', lambda p: V(p, 'b')), ('vc', lambda p: V(p, 'c'))], lambda p: E(p, A(p, A(p, 'a', 'b'), 'c'), A(p, 'a', A(p, 'b', 'c'))), 'G3.assoc(PM1, a, b, c, $va, $vb, $vc)'),
    ('Group.identity', 'A + O is A', [('a', SP)], [], lambda p: E(p, A(p, 'a', 'CS.infinity()'), 'a'), 'G2.unit(PM1, a)'),
    ('Group.inverse', 'A + (-A) is O', [('a', SP)], [], lambda p: E(p, A(p, 'a', 'GS.neg(%s, a)' % p), 'CS.infinity()'), 'G2.inv(PM1, a)'),
    ('Group.double', 'the doubling program is A + A, as triples', [('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: '{CS.pdbl(%s, a) == %s : CS.SPoint}' % (p, A(p, 'a', 'a')), 'G2.dbl(PM1, a, $va)'),
    ('Equiv.refl', 'equiv is reflexive', [('a', SP)], [], lambda p: E(p, 'a', 'a'), 'G2.e_refl(PM1, a)'),
    ('Equiv.sym', 'equiv is symmetric', [('a', SP), ('b', SP)], [('h', lambda p: E(p, 'a', 'b'))], lambda p: E(p, 'b', 'a'), 'G2.e_sym(PM1, a, b, $h)'),
    ('Equiv.trans', 'equiv is transitive through a point of the group', [('a', SP), ('b', SP), ('c', SP)], [('vb', lambda p: V(p, 'b')), ('hab', lambda p: E(p, 'a', 'b')), ('hbc', lambda p: E(p, 'b', 'c'))], lambda p: E(p, 'a', 'c'), 'G2.e_trans(HPA, a, b, c, $vb, $hab, $hbc)'),
    ('Equiv.add_left', 'the addition respects equiv in its first argument', [('a', SP), ('a2', SP), ('b', SP)], [('va', lambda p: V(p, 'a')), ('va2', lambda p: V(p, 'a2')), ('h', lambda p: E(p, 'a', 'a2'))], lambda p: E(p, A(p, 'a', 'b'), A(p, 'a2', 'b')), 'G2.e_add_l(HPA, a, a2, b, $va, $va2, $h)'),
    ('Equiv.add_right', 'and in its second', [('a', SP), ('b', SP), ('b2', SP)], [('vb', lambda p: V(p, 'b')), ('vb2', lambda p: V(p, 'b2')), ('h', lambda p: E(p, 'b', 'b2'))], lambda p: E(p, A(p, 'a', 'b'), A(p, 'a', 'b2')), 'G2.e_add_r(HPA, a, b, b2, $vb, $vb2, $h)'),
    ('Scalar.closed', '[k] A is a point of the group', [('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: V(p, S(p, 'k', 'a')), 'G4.v_smul(FPA, k, a, $va)'),
    ('Scalar.add', '[j + k] A = [j] A + [k] A', [('j', 'Nat'), ('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: E(p, S(p, 'Nat.add(j, k)', 'a'), A(p, S(p, 'j', 'a'), S(p, 'k', 'a'))), 'G4.smul_add(FPA, j, k, a, $va)'),
    ('Scalar.mul', '[j k] A = [j] ([k] A)', [('j', 'Nat'), ('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: E(p, S(p, 'Nat.mul(j, k)', 'a'), S(p, 'j', S(p, 'k', 'a'))), 'G4.smul_mul(FPA, j, k, a, $va)'),
    ('Scalar.equiv', '[k] respects equiv', [('k', 'Nat'), ('a', SP), ('a2', SP)], [('va', lambda p: V(p, 'a')), ('va2', lambda p: V(p, 'a2')), ('h', lambda p: E(p, 'a', 'a2'))], lambda p: E(p, S(p, 'k', 'a'), S(p, 'k', 'a2')), 'G4.smul_eqv(FPA, k, a, a2, $va, $va2, $h)'),
    ('Scalar.pmul_closed', 'the double-and-add result is a point of the group', [('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: V(p, 'CS.pmul(%s, k, a)' % p), 'G4.pmul_valid(FPA, k, a, $va)'),
    ('Scalar.pmul_low', 'the double-and-add over 256 bits computes [k mod 2^256] A', [('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a'))], lambda p: E(p, 'CS.pmul(%s, k, a)' % p, S(p, 'C.low(256n, k)', 'a')), 'G4.pmul_low(FPA, k, a, $va)'),
    ('Scalar.pmul', 'for k < 2^256 the double-and-add computes [k] A', [('k', 'Nat'), ('a', SP)], [('va', lambda p: V(p, 'a')), ('hk', lambda p: '{C.fits(256n, k) == True{} : Bool}')], lambda p: E(p, 'CS.pmul(%s, k, a)' % p, S(p, 'k', 'a')), 'G4.pmul_smul(FPA, k, a, $va, hk)'),
]
HPT = 'PM.Prime(FS.prime(one))'
HCT = '{Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}'
MACROS = {'FPA': 'GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1)',
          'HPA': 'GF.pm(one), GF.hp_m(one, h1, hp)', 'PM1': 'GF.pm(one)', 'H21': 'GF.h21_m(one, h1)'}


def lname(name):
    return name.lower().replace('.', '_')


def main():
    gp = '''# GENERATED by tools/generators/secp256k1_group/gen_laws.py; edit the generator
import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/group.bend as GS
import ../../../lib/logic.bend as Lg
import ../../../math/number/nt_prime.bend as PM
import ./gfp.bend as GF
import ./glaw1.bend as G1
import ./glaw2.bend as G2
import ./glaw3.bend as G3
import ./glaw4.bend as G4
import ./certb.bend as CB

# The group-law clauses of laws_group.bend on the modulus FS.prime(one),
# each with the two facts about p as hypotheses:
#   hp: p is prime;  hc: (-7)^((p - 1) / 3) != 1 in GF(p)
# (their certificates, group/certa.bend and group/certd.bend, are closed
# computations too heavy to import beside other proofs: a proof that uses
# the group law takes hp and hc and leaves them to its closing root). Each
# is the lemma of glaw1..4.bend for the modulus 1 + pm, moved along
# FS.prime(one) == 1 + pm (certb.bend).
'''
    laws = '''# GENERATED by tools/generators/secp256k1_group/gen_laws.py; edit the generator
import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS

# The group law of secp256k1 on the specification's projective points
# (spec/crypto/secp256k1/curve.bend: the complete Renes-Costello-Batina
# addition padd, the doubling pdbl, the double-and-add pmul; and
# spec/crypto/secp256k1/group.bend: valid, equiv, neg, smul). Every clause
# is for every input; `one` is the number 1 kept symbolic (h1), as in the
# other secp256k1 clauses. Proved by
# `bend proofs/crypto/secp256k1/proof_group.bend`, from the lemmas of
# proofs/crypto/secp256k1/group/ and the certificates that
# p = 2^256 - 2^32 - 977 is prime and that -7 is not a cube modulo p.
'''
    proof = '''# GENERATED by tools/generators/secp256k1_group/gen_laws.py; edit the generator
import Base
import ./laws_group.bend as Laws
import ./group/glawp.bend as GP
import ./group/certa.bend as CA
import ./group/certd.bend as CD

# The group law of secp256k1 (laws_group.bend):
# `bend proofs/crypto/secp256k1/proof_group.bend`. Each clause is its lemma
# of group/glawp.bend applied to the two certificates: p is prime
# (group/certa.bend) and (-7)^((p - 1) / 3) != 1 (group/certd.bend).
'''
    for name, com, vs, hyps, concl, pr in LAWS:
        for k in sorted(MACROS, key=len, reverse=True):
            pr = re.sub(r'\b%s\b' % k, MACROS[k], pr)
        for h, t in hyps:
            pr = re.sub(r'\$%s\b' % h, 'Lg.subst(Nat, p => %s, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), %s)' % (t('p'), h), pr)
        params = ''.join(', +%s: %s' % (v, t) for v, t in vs) + ''.join(', +%s: %s' % (h, t(P)) for h, t in hyps)
        gp += '\n# %s\ndef %s(+one: Nat, +h1: {one == 1n : Nat}, +hp: %s, +hc: %s%s) -> %s:\n  Lg.subst(Nat, p => %s, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), %s)\n' % (
            com, lname(name), HPT, HCT, params, concl(P), concl('p'), pr)
        laws += '\n# %s\nlaw %s:\n  for +one: Nat\n  for +h1: {one == 1n : Nat}\n' % (com, name)
        for v, t in vs:
            laws += '  for +%s: %s\n' % (v, t)
        for h, t in hyps:
            laws += '  for +%s: %s\n' % (h, t(P))
        laws += '  %s\n' % concl(P)
        args = [v for v, _ in vs] + [h for h, _ in hyps]
        proof += '\ndef Laws.%s(%s):\n  GP.%s(%s)\n' % (name, ', '.join(['one', 'h1'] + args), lname(name), ', '.join(['one', 'h1', 'CA.prime_p(one, h1)', 'CD.cube_spec(one, h1)'] + args))
    open(os.path.join(OUT, 'group', 'glawp.bend'), 'w').write(gp)
    open(os.path.join(OUT, 'laws_group.bend'), 'w').write(laws)
    open(os.path.join(OUT, 'proof_group.bend'), 'w').write(proof)


if __name__ == '__main__':
    main()
