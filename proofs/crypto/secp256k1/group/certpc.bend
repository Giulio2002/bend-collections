import Base
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../math/number/nt_prime.bend as PM
import ./certa.bend as CA
import ./certd.bend as CD

# The two closed facts about secp256k1's p that the group law needs, from
# one shared computation (cert_p.bend: the Pocklington chain p <- q1 <- r2,
# whose power 49^((p-1)/6) at level p is also (p - 7)^((p-1)/3)).

# p is prime
def prime_p(+one: Nat, +h1: {one == 1n : Nat}) -> PM.Prime(FS.prime(one)):
  CA.prime_p(one, h1)

# (-7)^((p - 1) / 3) != 1 in GF(p): -7 is not a cube
def cube_spec(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}:
  CD.cube_spec(one, h1)
