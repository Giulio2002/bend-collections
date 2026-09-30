import Base
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../../spec/crypto/secp256k1/affine.bend as GA
import ../../math/number/nt_prime.bend as PM

# The affine group law of secp256k1 (SEC 1 section 2.2.1;
# spec/crypto/secp256k1/affine.bend: points (x, y) of y^2 = x^3 + 7 with the
# point at infinity, the chord-and-tangent addition GA.add) and its
# correspondence with the specification's complete projective addition
# (GA.of_proj: (X : Y : Z) to (X / Z, Y / Z), infinity when Z = 0).
# Every clause is for every input and unconditional: the closing root
# applies the certificates (p prime, (-7)^((p-1)/3) != 1).
# Proved by `bend proofs/crypto/secp256k1/proof_affine.bend`.

# the point at infinity is the identity (by definition of GA.add)
law Affine.identity_right:
  for +p: Nat
  for +a: GA.APoint
  {GA.add(p, a, GA.AInf{}) == a : GA.APoint}

law Affine.identity_left:
  for +p: Nat
  for +a: GA.APoint
  {GA.add(p, GA.AInf{}, a) == a : GA.APoint}

# the complete projective addition computes the chord-and-tangent addition of the affine points
law Affine.sum:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  {GA.of_proj(FS.prime(one), CS.padd(FS.prime(one), a, b)) == GA.add(FS.prime(one), GA.of_proj(FS.prime(one), a), GA.of_proj(FS.prime(one), b)) : GA.APoint}

# equiv points of the group have the same affine point
law Affine.of_equiv:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  for +h: {GS.equiv(FS.prime(one), a, b) == True{} : Bool}
  {GA.of_proj(FS.prime(one), a) == GA.of_proj(FS.prime(one), b) : GA.APoint}

# and conversely
law Affine.equiv_of:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: CS.SPoint
  for +b: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GS.valid(FS.prime(one), b) == True{} : Bool}
  for +h: {GA.of_proj(FS.prime(one), a) == GA.of_proj(FS.prime(one), b) : GA.APoint}
  {GS.equiv(FS.prime(one), a, b) == True{} : Bool}

# the affine point of a point of the group is on the curve, with coordinates below p
law Affine.of_valid:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: CS.SPoint
  for +va: {GS.valid(FS.prime(one), a) == True{} : Bool}
  {GA.valid(FS.prime(one), GA.of_proj(FS.prime(one), a)) == True{} : Bool}

# an affine point of the curve is a projective point of the group
law Affine.to_valid:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  {GS.valid(FS.prime(one), GA.to_proj(a)) == True{} : Bool}

# and it is its affine point
law Affine.of_to:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  {GA.of_proj(FS.prime(one), GA.to_proj(a)) == a : GA.APoint}

# the sum of two points of the curve is a point of the curve
law Affine.closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +b: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GA.valid(FS.prime(one), b) == True{} : Bool}
  {GA.valid(FS.prime(one), GA.add(FS.prime(one), a, b)) == True{} : Bool}

# A + B = B + A
law Affine.commutative:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +b: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GA.valid(FS.prime(one), b) == True{} : Bool}
  {GA.add(FS.prime(one), a, b) == GA.add(FS.prime(one), b, a) : GA.APoint}

# (A + B) + C = A + (B + C)
law Affine.associative:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +b: GA.APoint
  for +c: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  for +vb: {GA.valid(FS.prime(one), b) == True{} : Bool}
  for +vc: {GA.valid(FS.prime(one), c) == True{} : Bool}
  {GA.add(FS.prime(one), GA.add(FS.prime(one), a, b), c) == GA.add(FS.prime(one), a, GA.add(FS.prime(one), b, c)) : GA.APoint}

# A + (-A) = O
law Affine.inverse:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  {GA.add(FS.prime(one), a, GA.neg(FS.prime(one), a)) == GA.AInf{} : GA.APoint}

# -A is a point of the curve
law Affine.neg_closed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: GA.APoint
  for +va: {GA.valid(FS.prime(one), a) == True{} : Bool}
  {GA.valid(FS.prime(one), GA.neg(FS.prime(one), a)) == True{} : Bool}
