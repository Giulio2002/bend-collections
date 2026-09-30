import Base
import ../../../spec/math/number.bend as SN
import ../../../spec/crypto/secp256k1/field.bend as FS

# The group order n of secp256k1 is prime (SN.prime: the trial-division
# predicate of spec/math/number.bend), for every `one` with h1. Proved by
# `bend proofs/crypto/secp256k1/proof_field_n.bend` (a Pocklington
# certificate; a root of its own because of its size).

# n is prime
law Field.order_prime:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {SN.prime(FS.order(one)) == True{} : Bool}
