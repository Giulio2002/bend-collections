import Base
import ../../lib/common.bend as C
import ../../../src/crypto/curve25519/field.bend as F

# GF(p), p = 2^255 - 19, over the natural numbers, and the contract of
# src/crypto/curve25519/field.bend.
#
# The checker keeps every closed natural number it compares in unary, so
# 2^255 is never written closed: it is C.shift(255n, one), with `one` a
# variable that every clause takes together with the hypothesis
# {one == 1n : Nat}. For one == 1 these are the usual constants; no other
# value of `one` satisfies the hypothesis, so each clause says exactly what
# it says with the constants written out. (The same device as the proofs of
# spec/math/w64.bend, which keep 2^32 as a shift of a symbolic one.)
#
# Representation: a field element is a list of U32 limbs, little-endian in
# radix 2^8 (value = RFC 7748's decodeLittleEndian); "tight" is 32 limbs,
# each below 2^8, which is also a 32-byte string.
#
#   function          clauses
#   add               Add.value, Add.tight
#   sub               Sub.value, Sub.tight
#   mul, sq           Mul.value, Mul.tight, Sq.value, Sq.tight
#   mul_small         MulSmall.value, MulSmall.tight
#   select            Select.zero, Select.one
#   inv               Inv.value, Inv.tight
#   pow_p58           PowP58.value, PowP58.tight
#   freeze, to_bytes  Freeze.value (the canonical representative), Freeze.tight
#   of_bytes          OfBytes.value (bit 255 ignored), OfBytes.tight
#   eq, is_zero       Eq.value, IsZero.value
#   parity            Parity.value

# decodeLittleEndian (RFC 7748 section 5): sum of b_i 2^(8 i)
def value(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(U32.to_nat(h), C.shift(8n, value(t)))

# n values, each below 2^8
def bytes_ok(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          True{}
        case Con{x, xt}:
          False{}
    case 1n+m:
      match xs:
        case Nil{}:
          False{}
        case Con{x, xt}:
          Bool.and(Nat.is_lt(U32.to_nat(x), 256n), bytes_ok(m, xt))

def tight(xs: List<&2, U32>) -> Bool:
  bytes_ok(32n, xs)

# a constant from its little-endian base-256 digits, each scaled by the
# symbolic one (so the checker never unfolds it): digits(one, [65n, 219n, 1n])
# is 121665 for one == 1
def digits(+one: Nat, ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, dt}:
      Nat.add(Nat.mul(one, d), C.shift(8n, digits(one, dt)))

# p = 2^255 - 19
def prime(+one: Nat) -> Nat:
  Nat.sub(C.shift(255n, one), 19n)

# arithmetic mod p (every result reduced)
def fadd(+p: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.add(a, b), p)

def fsub(+p: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.sub(Nat.add(a, p), Nat.mod(b, p)), p)

def fmul(+p: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.mul(a, b), p)

def fpow(+p: Nat, a: Nat, e: Nat) -> Nat:
  Nat.mod(Nat.pow(a, e), p)

# a^(p - 2): the inverse of a nonzero a (Fermat), 0 for 0 (RFC 7748 section 5)
def finv(+p: Nat, a: Nat) -> Nat:
  fpow(p, a, Nat.sub(p, 2n))

# ---- clauses ----

def Add.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.add(a, b)), prime(one)) == fadd(prime(one), value(a), value(b)) : Nat}

def Add.tight(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {tight(F.add(a, b)) == True{} : Bool}

def Sub.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.sub(a, b)), prime(one)) == fsub(prime(one), value(a), value(b)) : Nat}

def Sub.tight(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {tight(F.sub(a, b)) == True{} : Bool}

def Mul.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.mul(a, b)), prime(one)) == fmul(prime(one), value(a), value(b)) : Nat}

def Mul.tight(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {tight(F.mul(a, b)) == True{} : Bool}

def Sq.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.sq(a)), prime(one)) == fmul(prime(one), value(a), value(a)) : Nat}

def Sq.tight(+a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {tight(F.sq(a)) == True{} : Bool}

# k below 2^17
def MulSmall.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +k: U32, +ha: {tight(a) == True{} : Bool}, +hk: {Nat.is_lt(U32.to_nat(k), C.shift(17n, one)) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.mul_small(a, k)), prime(one)) == fmul(prime(one), value(a), U32.to_nat(k)) : Nat}

def MulSmall.tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +k: U32, +ha: {tight(a) == True{} : Bool}, +hk: {Nat.is_lt(U32.to_nat(k), C.shift(17n, one)) == True{} : Bool}) -> Type:
  {tight(F.mul_small(a, k)) == True{} : Bool}

def Select.zero(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {F.select(0, a, b) == a : List<&2, U32>}

def Select.one(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {F.select(1, a, b) == b : List<&2, U32>}

def Inv.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.inv(a)), prime(one)) == finv(prime(one), value(a)) : Nat}

def Inv.tight(+a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {tight(F.inv(a)) == True{} : Bool}

# a^((p - 5) / 8), RFC 8032 section 5.1.3
def PowP58.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {Nat.mod(value(F.pow_p58(a)), prime(one)) == fpow(prime(one), value(a), Nat.div(Nat.sub(prime(one), 5n), 8n)) : Nat}

def PowP58.tight(+a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {tight(F.pow_p58(a)) == True{} : Bool}

# the canonical representative, which is the 32-byte encoding
def Freeze.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {value(F.freeze(a)) == Nat.mod(value(a), prime(one)) : Nat}

def Freeze.tight(+a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {tight(F.freeze(a)) == True{} : Bool}

def OfBytes.value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {tight(bs) == True{} : Bool}) -> Type:
  {value(F.of_bytes(bs)) == Nat.mod(value(bs), C.shift(255n, one)) : Nat}

def OfBytes.tight(+bs: List<&2, U32>, +hb: {tight(bs) == True{} : Bool}) -> Type:
  {tight(F.of_bytes(bs)) == True{} : Bool}

def Eq.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {tight(a) == True{} : Bool}, +hb: {tight(b) == True{} : Bool}) -> Type:
  {F.eq(a, b) == Nat.is_eq(Nat.mod(value(a), prime(one)), Nat.mod(value(b), prime(one))) : Bool}

def IsZero.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {F.is_zero(a) == Nat.is_eq(Nat.mod(value(a), prime(one)), 0n) : Bool}

def Parity.value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {tight(a) == True{} : Bool}) -> Type:
  {U32.to_nat(F.parity(a)) == Nat.mod(Nat.mod(value(a), prime(one)), 2n) : Nat}
