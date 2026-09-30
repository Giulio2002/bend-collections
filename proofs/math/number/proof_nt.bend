import Base
import ./nt_prime.bend as PM
import ./nt_flt.bend as FL
import ./nt_fld.bend as FD
import ./nt_ord.bend as OR
import ./nt_mf.bend as MF
import ./nt_pock.bend as PK

# Number theory for prime moduli (used by the elliptic-curve group laws), in
# one root (`bend proofs/math/number/proof_nt.bend`): primes and Euclid's
# lemma (nt_prime.bend), Fermat's little theorem (nt_flt.bend), the field facts
# for a prime modulus (nt_fld.bend), least prime factors (nt_mf.bend) and
# Pocklington's criterion (nt_ord.bend, nt_pock.bend).

# a^p == a (mod p)
def fermat(+p: Nat, +hp: PM.Prime(p), +a: Nat) -> {Nat.mod(Nat.pow(a, p), p) == Nat.mod(a, p) : Nat}:
  FL.flt(p, hp, a)

# the Fermat inverse a^(p-2) mod p is the inverse, for a prime modulus
def inverse(+p: Nat, +hp: PM.Prime(p), +a: Nat, +ha: {Nat.is_eq(Nat.mod(a, p), 0n) == False{} : Bool}) -> {Nat.mod(Nat.mul(a, Nat.mod(Nat.pow(a, Nat.sub(p, 2n)), p)), p) == 1n : Nat}:
  FD.inv_mod(p, hp, a, ha)

# an example certificate: 7 is prime by Pocklington with F = 3
# (7 == 3 * 2 + 1, 3^6 mod 7 == 1, 3^2 mod 7 == 2, 1 * (2 - 1) == 0 * 7 + 1)
def seven() -> PM.Prime(7n):
  PK.pocklington(7n, 5n, {==}, [PK.PE{3n, 2n, 3n, 2n, 1n, 0n}],
    PK.cert_cons(7n, 3n, 2n, 3n, 2n, 1n, 0n, Nil{}, PM.small_prime(3n, {==}), {==}, {==}, {==}, {==}, {==}, PK.cert_nil(7n)),
    {==})
