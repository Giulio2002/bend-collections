import Base
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ./prime.bend as PM
import ./ntflt.bend as FL
import ./ntfld.bend as FD
import ./ntord.bend as OR
import ./ntmf.bend as MF
import ./ntpock.bend as PK

# The number theory of the secp256k1 group law, in one root
# (`bend proofs/crypto/secp256k1/group/proof_nt.bend`): primes and Euclid's
# lemma (prime.bend), Fermat's little theorem (ntflt.bend), the field facts
# for a prime modulus (ntfld.bend), least prime factors (ntmf.bend) and
# Pocklington's criterion (ntord.bend, ntpock.bend).

# a^p == a (mod p)
def fermat(+p: Nat, +hp: PM.Prime(p), +a: Nat) -> {Nat.mod(Nat.pow(a, p), p) == Nat.mod(a, p) : Nat}:
  FL.flt(p, hp, a)

# the specification's inverse is the inverse, for a prime modulus
def inverse(+p: Nat, +hp: PM.Prime(p), +a: Nat, +ha: {Nat.is_eq(Nat.mod(a, p), 0n) == False{} : Bool}) -> {FS.mmul(p, a, FS.minv(p, a)) == 1n : Nat}:
  FD.minv_ok(p, hp, a, ha)

# an example certificate: 7 is prime by Pocklington with F = 3
# (7 == 3 * 2 + 1, 3^6 mod 7 == 1, 3^2 mod 7 == 2, 1 * (2 - 1) == 0 * 7 + 1)
def seven() -> PM.Prime(7n):
  PK.pocklington(7n, 5n, {==}, [PK.PE{3n, 2n, 3n, 2n, 1n, 0n}],
    PK.cert_cons(7n, 3n, 2n, 3n, 2n, 1n, 0n, Nil{}, PM.small_prime(3n, {==}), {==}, {==}, {==}, {==}, {==}, PK.cert_nil(7n)),
    {==})
