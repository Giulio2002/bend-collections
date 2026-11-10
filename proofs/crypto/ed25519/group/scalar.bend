import Base
import ../../../../spec/math/number.bend as SN
import ../../../../spec/crypto/ed25519.bend as ED
import ../../../../spec/crypto/ed25519_group.bend as GE
import ./lite/math/number/nt_fld.bend as FD

# The scalars modulo the group order L are a field, for L prime (the
# Pocklington certificate: certla.bend, cert_l.bend, cert_l1.bend).

def inverse(+one: Nat, +h1: {one == 1n : Nat}, +hp: {SN.prime(ED.ell(one)) == True{} : Bool}, +a: Nat, +ha: {Nat.is_eq(Nat.mod(a, ED.ell(one)), 0n) == False{} : Bool}) -> GE.Scalar.inverse(one, h1, hp, a, ha):
  FD.inv_mod(ED.ell(one), hp, a, ha)

def no_zero_div(+one: Nat, +h1: {one == 1n : Nat}, +hp: {SN.prime(ED.ell(one)) == True{} : Bool}, +a: Nat, +b: Nat, +hab: {Nat.mod(Nat.mul(a, b), ED.ell(one)) == 0n : Nat}, +ha: {Nat.is_eq(Nat.mod(a, ED.ell(one)), 0n) == False{} : Bool}) -> GE.Scalar.no_zero_div(one, h1, hp, a, b, hab, ha):
  FD.no_zero_div(ED.ell(one), hp, a, b, hab, ha)
