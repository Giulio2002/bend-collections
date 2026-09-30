import Base
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../../spec/crypto/secp256k1/encoding.bend as EN
import ../../math/number/nt_prime.bend as PM

# The SEC 1 public key encodings of the specification
# (spec/crypto/secp256k1/curve.bend: encode_uncompressed, encode_compressed,
# decode, with decompression by the square root a^((p + 1) / 4)) round trip,
# for every input; `one` is the number 1 kept symbolic (h1).
#
# The hypotheses are the facts about p proved in roots of their own
# (group/certa.bend, group/certd.bend), as in laws_group.bend: hp (p is
# prime) and, for the last clause only, hc ((-7)^((p - 1) / 3) != 1).
# Proved by `bend proofs/crypto/secp256k1/proof_encoding.bend`.

# the square root of a square squares to it: fsqrt(a)^2 == a for a == y0^2 (p == 3 mod 4)
law Sqrt.square:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +a: Nat
  for +y0: Nat
  for +ha: {Nat.mod(a, FS.prime(one)) == FS.mmul(FS.prime(one), y0, y0) : Nat}
  {FS.mmul(FS.prime(one), FS.fsqrt(FS.prime(one), a), FS.fsqrt(FS.prime(one), a)) == Nat.mod(a, FS.prime(one)) : Nat}

# of the two roots r, -r of y^2 the one with the parity of y is y
law Sqrt.parity:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +r: Nat
  for +y: Nat
  for +hr: {Nat.is_lt(r, FS.prime(one)) == True{} : Bool}
  for +hy: {Nat.is_lt(y, FS.prime(one)) == True{} : Bool}
  for +hsq: {FS.mmul(FS.prime(one), r, r) == FS.mmul(FS.prime(one), y, y) : Nat}
  {CS.pick_parity(FS.prime(one), r, Nat.mod(y, 2n)) == y : Nat}

# decode(04 || x || y) is (x : y : 1) for a point of the affine curve
law Encoding.uncompressed_affine:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +x: Nat
  for +y: Nat
  for +hx: {Nat.is_lt(x, FS.prime(one)) == True{} : Bool}
  for +hy: {Nat.is_lt(y, FS.prime(one)) == True{} : Bool}
  for +hc: {CS.on_curve(FS.prime(one), x, y) == True{} : Bool}
  {CS.decode(FS.prime(one), CS.encode_uncompressed(FS.prime(one), CS.SPoint{x, y, 1n})) == Some{CS.SPoint{x, y, 1n}} : Maybe<&2, CS.SPoint>}

# decode(02/03 || x) is (x : y : 1): decompression recovers y
law Encoding.compressed_affine:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +x: Nat
  for +y: Nat
  for +hx: {Nat.is_lt(x, FS.prime(one)) == True{} : Bool}
  for +hy: {Nat.is_lt(y, FS.prime(one)) == True{} : Bool}
  for +hc: {CS.on_curve(FS.prime(one), x, y) == True{} : Bool}
  {CS.decode(FS.prime(one), CS.encode_compressed(FS.prime(one), CS.SPoint{x, y, 1n})) == Some{CS.SPoint{x, y, 1n}} : Maybe<&2, CS.SPoint>}

# decode(encode(A)) is the affine form (X / Z : Y / Z : 1) of a point of the group with Z != 0
law Encoding.uncompressed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +hv: {GS.valid(FS.prime(one), CS.SPoint{x, y, z}) == True{} : Bool}
  for +hz: {Nat.is_eq(Nat.mod(z, FS.prime(one)), 0n) == False{} : Bool}
  {CS.decode(FS.prime(one), CS.encode_uncompressed(FS.prime(one), CS.SPoint{x, y, z})) == Some{CS.SPoint{FS.mmul(FS.prime(one), x, FS.minv(FS.prime(one), z)), FS.mmul(FS.prime(one), y, FS.minv(FS.prime(one), z)), 1n}} : Maybe<&2, CS.SPoint>}

# the same for the compressed encoding
law Encoding.compressed:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +hv: {GS.valid(FS.prime(one), CS.SPoint{x, y, z}) == True{} : Bool}
  for +hz: {Nat.is_eq(Nat.mod(z, FS.prime(one)), 0n) == False{} : Bool}
  {CS.decode(FS.prime(one), CS.encode_compressed(FS.prime(one), CS.SPoint{x, y, z})) == Some{CS.SPoint{FS.mmul(FS.prime(one), x, FS.minv(FS.prime(one), z)), FS.mmul(FS.prime(one), y, FS.minv(FS.prime(one), z)), 1n}} : Maybe<&2, CS.SPoint>}

# decode answers None or a point of the group in normal form (x : y : 1), x, y < p
law Encoding.decode_valid:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hp: PM.Prime(FS.prime(one))
  for +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
  for +bs: List<&2, U32>
  {EN.decoded_ok(FS.prime(one), CS.decode(FS.prime(one), bs)) == True{} : Bool}
