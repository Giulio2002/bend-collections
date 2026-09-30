import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../math/number/nt_prime.bend as PM

# The group law of secp256k1 on the specification's projective points
# (spec/crypto/secp256k1/curve.bend: the complete Renes-Costello-Batina
# addition padd, the doubling pdbl, the double-and-add pmul; and
# spec/crypto/secp256k1/group.bend: valid, equiv, neg, smul). Every clause
# is for every input; `one` is the number 1 kept symbolic (h1), as in the
# other secp256k1 clauses.
#
# Each clause takes two facts about p = 2^256 - 2^32 - 977 as hypotheses,
# because their certificates are closed computations that each fill a root
# of their own (group/certa.bend, group/certd.bend: `Field.prime` and
# `Field.cube` below are proved there, for every `one` with h1):
#   hp: p is prime (SN.prime(p) == True, the trial-division predicate of
#       spec/math/number.bend; proved by a Pocklington chain);
#   hc: (-7)^((p - 1) / 3) != 1 in GF(p) (so -7 is not a cube, the curve has
#       no point of order 2, and the addition formulas are complete).
# Proved by `bend proofs/crypto/secp256k1/proof_group.bend`.

# the sum of two points of the group is a point of the group
law Group.closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  {GS.valid(FS.prime(one), CS.padd(FS.prime(one), a, b)) == True{} : Bool}

# (0 : 1 : 0) is a point of the group
law Group.infinity:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  {GS.valid(FS.prime(one), CS.infinity()) == True{} : Bool}

# -A is a point of the group
law Group.neg_closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.valid(FS.prime(one), GS.neg(FS.prime(one), a)) == True{} : Bool}

# A + B = B + A, as triples
law Group.commutative:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  {CS.padd(FS.prime(one), a, b) == CS.padd(FS.prime(one), b, a) : CS.SPoint}

# (A + B) + C and A + (B + C) are the same projective point
law Group.associative:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +c: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  for +vc: {GS.valid(FS.prime(one), c) == True{} : Bool}
  {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), CS.padd(FS.prime(one), a, b), c), CS.padd(FS.prime(one), a, CS.padd(FS.prime(one), b, c))) == True{} : Bool}

# A + O is A
law Group.identity:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), a, CS.infinity()), a) == True{} : Bool}

# A + (-A) is O
law Group.inverse:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), a, GS.neg(FS.prime(one), a)), CS.infinity()) == True{} : Bool}

# the doubling program is A + A, as triples
law Group.double:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {CS.pdbl(FS.prime(one), a) == CS.padd(FS.prime(one), a, a) : CS.SPoint}

# equiv is reflexive
law Equiv.refl:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  {GS.equiv(FS.prime(one), a, a) == True{} : Bool}

# equiv is symmetric
law Equiv.sym:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +h: {GS.equiv(FS.prime(one), a, b) == True{} : Bool}
  {GS.equiv(FS.prime(one), b, a) == True{} : Bool}

# equiv is transitive through a point of the group
law Equiv.trans:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +c: CS.SPoint
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  for +hab: {GS.equiv(FS.prime(one), a, b) == True{} : Bool}
  for +hbc: {GS.equiv(FS.prime(one), b, c) == True{} : Bool}
  {GS.equiv(FS.prime(one), a, c) == True{} : Bool}

# the addition respects equiv in its first argument
law Equiv.add_left:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +a2: CS.SPoint
  for +b: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +va2: {GS.valid(FS.prime(one), a2) == True{} : Bool}
  for +h: {GS.equiv(FS.prime(one), a, a2) == True{} : Bool}
  {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), a, b), CS.padd(FS.prime(one), a2, b)) == True{} : Bool}

# and in its second
law Equiv.add_right:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +b2: CS.SPoint
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  for +vb2: {GS.valid(FS.prime(one), b2) == True{} : Bool}
  for +h: {GS.equiv(FS.prime(one), b, b2) == True{} : Bool}
  {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), a, b), CS.padd(FS.prime(one), a, b2)) == True{} : Bool}

# [k] A is a point of the group
law Scalar.closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.valid(FS.prime(one), GS.smul(FS.prime(one), k, a)) == True{} : Bool}

# [j + k] A = [j] A + [k] A
law Scalar.add:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +j: Nat
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), Nat.add(j, k), a), CS.padd(FS.prime(one), GS.smul(FS.prime(one), j, a), GS.smul(FS.prime(one), k, a))) == True{} : Bool}

# [j k] A = [j] ([k] A)
law Scalar.mul:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +j: Nat
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), Nat.mul(j, k), a), GS.smul(FS.prime(one), j, GS.smul(FS.prime(one), k, a))) == True{} : Bool}

# [k] respects equiv
law Scalar.equiv:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +k: Nat
  for +a: CS.SPoint
  for +a2: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +va2: {GS.valid(FS.prime(one), a2) == True{} : Bool}
  for +h: {GS.equiv(FS.prime(one), a, a2) == True{} : Bool}
  {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), k, a), GS.smul(FS.prime(one), k, a2)) == True{} : Bool}

# the double-and-add result is a point of the group
law Scalar.pmul_closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.valid(FS.prime(one), CS.pmul(FS.prime(one), k, a)) == True{} : Bool}

# the double-and-add over 256 bits computes [k mod 2^256] A
law Scalar.pmul_low:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GS.equiv(FS.prime(one), CS.pmul(FS.prime(one), k, a), GS.smul(FS.prime(one), C.low(256n, k), a)) == True{} : Bool}

# for k < 2^256 the double-and-add computes [k] A
law Scalar.pmul:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +k: Nat
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +hk: {C.fits(256n, k) == True{} : Bool}
  {GS.equiv(FS.prime(one), CS.pmul(FS.prime(one), k, a), GS.smul(FS.prime(one), k, a)) == True{} : Bool}
