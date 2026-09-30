import Base
import ../../lib/common.bend as C
import ./field.bend as FS
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS

# The fast field of src/crypto/curve25519/fe.bend (15 Nat limbs of 17
# bits) over the natural numbers: its value and limb bounds, and the
# contract of every operation (the same statements as field.bend's for the
# 8-bit limb lists, with the limb bounds of this representation). `one` is
# field.bend's symbolic 1; the radix every operation takes is
# FE.radix(one) = 2^17.
#
# An element is "ok" when every limb is below 2^19: every operation takes
# ok elements and returns ok elements. It is "canonical" when every limb is
# below 2^17 and its value is below p (freeze's result).
#
#   function            clauses
#   add, sub            Add.value, Add.ok, Sub.value, Sub.ok
#   mul, sq             Mul.value, Mul.ok, Sq.value, Sq.ok, Mul.fits,
#                       Sq.fits
#   mul_small           MulSmall.value, MulSmall.ok
#   select              Select.zero, Select.one
#   inv, pow_p58        Inv.value, Inv.ok, PowP58.value, PowP58.ok
#   freeze              Freeze.value, Freeze.canon
#   to_bytes            ToBytes.value, ToBytes.tight
#   of_bytes            OfBytes.value, OfBytes.ok
#   eq, is_zero         Eq.value, IsZero.value
#   parity              Parity.value
#   carry passes        Carry.fits
#
# Fits: the native backend keeps a Nat in one machine word below 2^48 (a
# larger value is a run-time error, never a wrong result); Mul.fits and
# Carry.fits bound the largest intermediates (the product's folded columns
# below 2^47, every carry-chain sum below 2^48). The limb products run on
# the native 32-bit multiplier (a limb below 2^19 times 9 or 10 bits of the
# other, below 2^29), where a Nat product would check its bound with a
# division.

# the value: sum of l_i 2^(17 i)
def lv(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(h, C.shift(17n, lv(t)))

def value(x: FE.Fe) -> Nat:
  lv(FE.to_list(x))

# every entry below b
def below(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      Bool.and(Nat.is_lt(x, b), below(xt, b))

def ok(+one: Nat, x: FE.Fe) -> Bool:
  below(FE.to_list(x), C.shift(19n, one))

def canon(+one: Nat, +x: FE.Fe) -> Bool:
  Bool.and(below(FE.to_list(x), C.shift(17n, one)), Nat.is_lt(value(x), FS.prime(one)))

# the sums of a carry chain (the largest Nat a carry pass forms)
def sums(+R: Nat, xs: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{Nat.add(h, c), sums(R, t, Nat.div(Nat.add(h, c), R))}

# ---- clauses ----

def Add.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.add(FE.radix(one), a, b)), FS.prime(one)) == FS.fadd(FS.prime(one), value(a), value(b)) : Nat}

def Add.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {ok(one, FE.add(FE.radix(one), a, b)) == True{} : Bool}

def Sub.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.sub(FE.radix(one), a, b)), FS.prime(one)) == FS.fsub(FS.prime(one), value(a), value(b)) : Nat}

def Sub.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {ok(one, FE.sub(FE.radix(one), a, b)) == True{} : Bool}

def Mul.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.mul(FE.radix(one), a, b)), FS.prime(one)) == FS.fmul(FS.prime(one), value(a), value(b)) : Nat}

def Mul.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {ok(one, FE.mul(FE.radix(one), a, b)) == True{} : Bool}

# the columns the product's carry pass takes (limb products through the
# 32-bit multiplier, LS.convp) are below 2^47
def Mul.fits(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {below(LS.fold(LS.convp(FE.to_list(a), FE.to_list(b))), C.shift(47n, one)) == True{} : Bool}

def Sq.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.sq(FE.radix(one), a)), FS.prime(one)) == FS.fmul(FS.prime(one), value(a), value(a)) : Nat}

def Sq.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {ok(one, FE.sq(FE.radix(one), a)) == True{} : Bool}

# the columns the square's carry pass takes (each cross product once,
# LS.sqp) are below 2^47
def Sq.fits(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {below(LS.fold(LS.sqp(FE.to_list(a))), C.shift(47n, one)) == True{} : Bool}

# k below 2^17
def MulSmall.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +k: Nat, +ha: {ok(one, a) == True{} : Bool}, +hk: {Nat.is_lt(k, C.shift(17n, one)) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.mul_small(FE.radix(one), a, k)), FS.prime(one)) == FS.fmul(FS.prime(one), value(a), k) : Nat}

def MulSmall.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +k: Nat, +ha: {ok(one, a) == True{} : Bool}, +hk: {Nat.is_lt(k, C.shift(17n, one)) == True{} : Bool}) -> Type:
  {ok(one, FE.mul_small(FE.radix(one), a, k)) == True{} : Bool}

def Select.zero(+a: FE.Fe, +b: FE.Fe) -> Type:
  {FE.select(0, a, b) == a : FE.Fe}

def Select.one(+a: FE.Fe, +b: FE.Fe) -> Type:
  {FE.select(1, a, b) == b : FE.Fe}

def Inv.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.inv(FE.radix(one), a)), FS.prime(one)) == FS.finv(FS.prime(one), value(a)) : Nat}

def Inv.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {ok(one, FE.inv(FE.radix(one), a)) == True{} : Bool}

def PowP58.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {Nat.mod(value(FE.pow_p58(FE.radix(one), a)), FS.prime(one)) == FS.fpow(FS.prime(one), value(a), Nat.div(Nat.sub(FS.prime(one), 5n), 8n)) : Nat}

def PowP58.ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {ok(one, FE.pow_p58(FE.radix(one), a)) == True{} : Bool}

def Freeze.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {value(FE.freeze(FE.radix(one), a)) == Nat.mod(value(a), FS.prime(one)) : Nat}

def Freeze.canon(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {canon(one, FE.freeze(FE.radix(one), a)) == True{} : Bool}

# the encoding is the canonical value's 32 little-endian bytes
def ToBytes.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {FS.value(FE.to_bytes(FE.radix(one), a)) == Nat.mod(value(a), FS.prime(one)) : Nat}

def ToBytes.tight(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {FS.tight(FE.to_bytes(FE.radix(one), a)) == True{} : Bool}

# 32 bytes, bit 255 dropped
def OfBytes.value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> Type:
  {value(FE.of_bytes(bs)) == Nat.mod(FS.value(bs), C.shift(255n, one)) : Nat}

def OfBytes.ok(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> Type:
  {ok(one, FE.of_bytes(bs)) == True{} : Bool}

def Eq.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {ok(one, a) == True{} : Bool}, +hb: {ok(one, b) == True{} : Bool}) -> Type:
  {FE.eq(FE.radix(one), a, b) == Nat.is_eq(Nat.mod(value(a), FS.prime(one)), Nat.mod(value(b), FS.prime(one))) : Bool}

def IsZero.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {FE.is_zero(FE.radix(one), a) == Nat.is_eq(Nat.mod(value(a), FS.prime(one)), 0n) : Bool}

def Parity.value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {ok(one, a) == True{} : Bool}) -> Type:
  {U32.to_nat(FE.parity(FE.radix(one), a)) == Nat.mod(Nat.mod(value(a), FS.prime(one)), 2n) : Nat}

# a carry pass over limbs below 2^47 forms only sums below 2^48
def Carry.fits(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +hx: {below(xs, C.shift(47n, one)) == True{} : Bool}) -> Type:
  {below(sums(FE.radix(one), xs, 0n), C.shift(48n, one)) == True{} : Bool}
