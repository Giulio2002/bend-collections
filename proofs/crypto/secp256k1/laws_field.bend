import Base
import ../../../spec/math/number.bend as SN
import ../../../spec/crypto/secp256k1/field.bend as FS

# The arithmetic facts about secp256k1's two moduli that the group law
# rests on, for every `one` with h1 (the number 1 kept symbolic, as in the
# other secp256k1 clauses): p = 2^256 - 2^32 - 977 is prime (the group
# order n: laws_field_n.bend; SN.prime is the trial-division predicate of
# spec/math/number.bend: 2 <= m and no d in [2, m) divides m), and -7 is
# not a cube modulo p (Euler's criterion: (-7)^((p - 1) / 3) != 1), so the
# curve y^2 = x^3 + 7 has no point with y = 0.
# Proved by `bend proofs/crypto/secp256k1/proof_field.bend` (Pocklington
# certificates: closed computations on binary numbers).

# p is prime
law Field.prime:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {SN.prime(FS.prime(one)) == True{} : Bool}

# (-7)^((p - 1) / 3) != 1 in GF(p)
law Field.not_cube:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}
