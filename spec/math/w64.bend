import Base
import ../lib/common.bend as C
import ../../src/math/u64.bend as W
import ../../src/math/w64.bend as X
import ../../src/math/natural.bend as M

# Specification of src/math/w64.bend: unsigned 64-bit arithmetic on the
# two-limb U64 (low limb first). value(a) is the natural number a denotes;
# every operation is the Nat operation modulo 2^64 (C.low(64n, _): the
# checker never forms 2^64; spec/lib/common.bend), as in
# spec/math/u64.bend's word model (the two agree: value(a) is
# unsigned(64, bits(a))).
#
# STATED, TESTED, NOT PROVED: w64.bend is the U64 instance's engine; its
# clauses are exercised through tools/check_generic.py (every generic
# function at U64 against Python integers) and tools/check_f64.py (the
# software binary64's significand arithmetic), not proved.
#
#   function          clauses
#   mul32             Mul32.value
#   add, add_over     Add.value, AddOver.value
#   sub               Sub.value
#   mul, mul_over     Mul.value, MulOver.value
#   half, odd         Half.value, Odd.value
#   lt, le, eq,       Lt.value, Le.value, Eq.value, IsZero.value
#   is_zero
#   div32, mod32      Div32.quot, Div32.rem, Mod32.value
#   quot, rem         DivMod.quot, DivMod.rem
#   mulmod            MulMod.value
#   isqrt, isqrt32    Isqrt.value, Isqrt32.value
#   shl, shr,         Shl.value, Shr.value, ShrJam.value
#   shr_jam
#   clz               Clz.value

def value(a: W.U64) -> Nat:
  match a:
    case W.U64{lo, hi}:
      Nat.add(U32.to_nat(lo), C.shift(32n, U32.to_nat(hi)))

# the U64 of a value below 2^64
def of_nat(+n: Nat) -> W.U64:
  W.U64{U32.from_nat(C.low(32n, n)), U32.from_nat(C.high(32n, n))}

def Mul32.value(+a: U32, +b: U32) -> Type:
  {value(X.mul32(a, b)) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

def Add.value(+a: W.U64, +b: W.U64) -> Type:
  {value(X.add(a, b)) == C.low(64n, Nat.add(value(a), value(b))) : Nat}

def AddOver.value(+a: W.U64, +b: W.U64) -> Type:
  {X.add_over(a, b) == Bool.not(C.fits(64n, Nat.add(value(a), value(b)))) : Bool}

def Sub.value(+a: W.U64, +b: W.U64, +h: {Nat.is_le(value(b), value(a)) == True{} : Bool}) -> Type:
  {value(X.sub(a, b)) == Nat.sub(value(a), value(b)) : Nat}

def Mul.value(+a: W.U64, +b: W.U64) -> Type:
  {value(X.mul(a, b)) == C.low(64n, Nat.mul(value(a), value(b))) : Nat}

def MulOver.value(+a: W.U64, +b: W.U64) -> Type:
  {X.mul_over(a, b) == Bool.not(C.fits(64n, Nat.mul(value(a), value(b)))) : Bool}

def Half.value(+a: W.U64) -> Type:
  {value(X.half(a)) == Nat.div(value(a), 2n) : Nat}

def Odd.value(+a: W.U64) -> Type:
  {X.odd(a) == Nat.is_eq(Nat.mod(value(a), 2n), 1n) : Bool}

def Lt.value(+a: W.U64, +b: W.U64) -> Type:
  {X.lt(a, b) == Nat.is_lt(value(a), value(b)) : Bool}

def Le.value(+a: W.U64, +b: W.U64) -> Type:
  {X.le(a, b) == Nat.is_le(value(a), value(b)) : Bool}

def Eq.value(+a: W.U64, +b: W.U64) -> Type:
  {X.eq(a, b) == Nat.is_eq(value(a), value(b)) : Bool}

def IsZero.value(+a: W.U64) -> Type:
  {X.is_zero(a) == Nat.is_eq(value(a), 0n) : Bool}

def Div32.quot(+a: W.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> Type:
  {value(X.fst_q(X.div32(a, d))) == Nat.div(value(a), U32.to_nat(d)) : Nat}

def Div32.rem(+a: W.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> Type:
  {U32.to_nat(X.snd_r(X.div32(a, d))) == Nat.mod(value(a), U32.to_nat(d)) : Nat}

def Mod32.value(+a: W.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> Type:
  {U32.to_nat(X.mod32(a, d)) == Nat.mod(value(a), U32.to_nat(d)) : Nat}

def DivMod.quot(+a: W.U64, +b: W.U64, +hb: {X.is_zero(b) == False{} : Bool}) -> Type:
  {value(X.quot(a, b)) == Nat.div(value(a), value(b)) : Nat}

def DivMod.rem(+a: W.U64, +b: W.U64, +hb: {X.is_zero(b) == False{} : Bool}) -> Type:
  {value(X.rem(a, b)) == Nat.mod(value(a), value(b)) : Nat}

# a, b < m: the product reduced, with no 64-bit overflow on the way
def MulMod.value(+a: W.U64, +b: W.U64, +m: W.U64, +ha: {Nat.is_lt(value(a), value(m)) == True{} : Bool}, +hb: {Nat.is_lt(value(b), value(m)) == True{} : Bool}) -> Type:
  {value(X.mulmod(a, b, m)) == Nat.mod(Nat.mul(value(a), value(b)), value(m)) : Nat}

# the integer square root of the proved Nat reference
def Isqrt.value(+n: W.U64) -> Type:
  {value(X.isqrt(n)) == M.isqrt(value(n)) : Nat}

def Isqrt32.value(+x: U32) -> Type:
  {U32.to_nat(X.isqrt32(x)) == M.isqrt(U32.to_nat(x)) : Nat}

def Shl.value(+a: W.U64, +k: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> Type:
  {value(X.shl(a, k)) == C.low(64n, C.shift(k, value(a))) : Nat}

def Shr.value(+a: W.U64, +k: Nat) -> Type:
  {value(X.shr(a, k)) == C.high(k, value(a)) : Nat}

# shifted right, with the shifted-out bits OR-ed into bit 0 (SoftFloat's
# softfloat_shiftRightJam64); jam(q, r) sets q's bit 0 when r is nonzero
def jam(+q: Nat, +r: Nat) -> Nat:
  Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(Nat.mod(q, 2n), Nat.min(r, 1n)))

def ShrJam.value(+a: W.U64, +k: Nat) -> Type:
  {value(X.shr_jam(a, k)) == jam(C.high(k, value(a)), C.low(k, value(a))) : Nat}

# 64 for zero
def Clz.value(+a: W.U64) -> Type:
  {X.clz(a) == Nat.sub(64n, M.bit_length(value(a))) : Nat}
