import Base
import ../lib/common.bend as C
import ../../src/math/fixed.bend as F
import ./number.bend as SN

# Specification of src/math/fixed.bend: fixed-width integer operations as
# Rust defines them for u32/u64 (python_style_math_stdlib_design.pdf
# section 2.6: checked_add, wrapping_add, saturating_add, overflowing_add
# families; section 3.2 bit_count and to_bytes/from_bytes; section 10
# is_prime / next_prime).
#
# Each clause is stated once over an instance model and read at U32
# (U32.to_nat, width 32) and U64 (spec/math/w64.bend's value, width 64):
#   val: T -> Nat, the value;  w, the width;  f, the function.
# Widths are written with C.fits, C.low, C.high and C.shift (spec/lib/
# common.bend): the checker never forms 2^32 or 2^64.
#
#   family        clauses (Rust u32/u64 documentation)
#   checked_*     CheckedAdd/Sub/Mul/Div/Rem/Pow/Shl/Shr.value: the exact
#                 result when it fits (divisor nonzero, shift below w),
#                 None otherwise
#   wrapping_*    WrappingAdd/Mul/Pow/Shl/Shr.value: the result mod 2^w
#                 (shift amount mod w); WrappingSub.value: r + b ==
#                 a + 2^w * [a < b]
#   saturating_*  SaturatingAdd/Mul/Pow.value: the result when it fits,
#                 else the largest value (fits w, +1 does not);
#                 SaturatingSub.value: a - b floored at 0
#   overflowing_* OverflowingX.value (the wrapping value) and
#                 OverflowingX.flag (the result did not fit / a < b /
#                 shift >= w)
#   bit_count     BitCount.value: spec/math/number.bend's ones(w, value)
#   is_prime      IsPrime.value (U32): spec/math/number.bend's prime
#   next_prime    NextPrime.found, NextPrime.none (U32): the least prime
#                 above n below 2^32, or None when there is none
#   to_bytes_*    ToBytes.le, ToBytes.be: the w/8 base-256 digits
#   from_bytes_*  FromBytes.le, FromBytes.be: the value of exactly w/8
#                 digits below 256, None for any other list

# ---- shared definitions ----

def mval(~T: Data, ~val: T -> Nat, r: Maybe<&2, T>) -> Maybe<&2, Nat>:
  match r:
    case Some{x}:
      Some{val(x)}
    case None{}:
      None{}

def keep(ok: Bool, +n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# n when it fits w bits
def cnat(+w: Nat, +n: Nat) -> Maybe<&2, Nat>:
  keep(C.fits(w, n), n)

def ov_val(~T: Data, ~val: T -> Nat, r: F.Over<T>) -> Nat:
  match r:
    case F.OV{v, f}:
      val(v)

def ov_flag(-T: Data, r: F.Over<T>) -> Bool:
  match r:
    case F.OV{v, f}:
      f

def bn(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# r is n when n fits w bits, and the largest w-bit value otherwise
def saturated(+w: Nat, +n: Nat, +r: Nat, ok: Bool) -> Bool:
  match ok:
    case True{}:
      Nat.is_eq(r, n)
    case False{}:
      Bool.and(C.fits(w, r), Bool.not(C.fits(w, 1n+r)))

# ---- checked ----

def CheckedAdd.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> Maybe<&2, T>, +w: Nat, +a: T, +b: T) -> Type:
  {mval(~T, ~val, f(a, b)) == cnat(w, Nat.add(val(a), val(b))) : Maybe<&2, Nat>}

def CheckedSub.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> Maybe<&2, T>, +a: T, +b: T) -> Type:
  {mval(~T, ~val, f(a, b)) == keep(Nat.is_le(val(b), val(a)), Nat.sub(val(a), val(b))) : Maybe<&2, Nat>}

def CheckedMul.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> Maybe<&2, T>, +w: Nat, +a: T, +b: T) -> Type:
  {mval(~T, ~val, f(a, b)) == cnat(w, Nat.mul(val(a), val(b))) : Maybe<&2, Nat>}

def CheckedDiv.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> Maybe<&2, T>, +a: T, +b: T) -> Type:
  {mval(~T, ~val, f(a, b)) == keep(Bool.not(Nat.is_eq(val(b), 0n)), Nat.div(val(a), val(b))) : Maybe<&2, Nat>}

def CheckedRem.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> Maybe<&2, T>, +a: T, +b: T) -> Type:
  {mval(~T, ~val, f(a, b)) == keep(Bool.not(Nat.is_eq(val(b), 0n)), Nat.mod(val(a), val(b))) : Maybe<&2, Nat>}

def CheckedPow.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> Maybe<&2, T>, +w: Nat, +a: T, +e: U32) -> Type:
  {mval(~T, ~val, f(a, e)) == cnat(w, Nat.pow(val(a), U32.to_nat(e))) : Maybe<&2, Nat>}

def CheckedShl.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> Maybe<&2, T>, +w: Nat, +a: T, +s: U32) -> Type:
  {mval(~T, ~val, f(a, s)) == keep(Nat.is_lt(U32.to_nat(s), w), C.low(w, C.shift(U32.to_nat(s), val(a)))) : Maybe<&2, Nat>}

def CheckedShr.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> Maybe<&2, T>, +w: Nat, +a: T, +s: U32) -> Type:
  {mval(~T, ~val, f(a, s)) == keep(Nat.is_lt(U32.to_nat(s), w), C.high(U32.to_nat(s), val(a))) : Maybe<&2, Nat>}

# ---- wrapping ----

def WrappingAdd.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +w: Nat, +a: T, +b: T) -> Type:
  {val(f(a, b)) == C.low(w, Nat.add(val(a), val(b))) : Nat}

def WrappingSub.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +w: Nat, +a: T, +b: T) -> Type:
  {Nat.add(val(f(a, b)), val(b)) == Nat.add(val(a), C.shift(w, bn(Nat.is_lt(val(a), val(b))))) : Nat}

def WrappingMul.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +w: Nat, +a: T, +b: T) -> Type:
  {val(f(a, b)) == C.low(w, Nat.mul(val(a), val(b))) : Nat}

def WrappingPow.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> T, +w: Nat, +a: T, +e: U32) -> Type:
  {val(f(a, e)) == C.low(w, Nat.pow(val(a), U32.to_nat(e))) : Nat}

def WrappingShl.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> T, +w: Nat, +a: T, +s: U32) -> Type:
  {val(f(a, s)) == C.low(w, C.shift(Nat.mod(U32.to_nat(s), w), val(a))) : Nat}

def WrappingShr.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> T, +w: Nat, +a: T, +s: U32) -> Type:
  {val(f(a, s)) == C.high(Nat.mod(U32.to_nat(s), w), val(a)) : Nat}

# ---- saturating ----

def SaturatingAdd.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +w: Nat, +a: T, +b: T) -> Type:
  {saturated(w, Nat.add(val(a), val(b)), val(f(a, b)), C.fits(w, Nat.add(val(a), val(b)))) == True{} : Bool}

def SaturatingSub.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +a: T, +b: T) -> Type:
  {val(f(a, b)) == Nat.sub(val(a), val(b)) : Nat}

def SaturatingMul.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> T, +w: Nat, +a: T, +b: T) -> Type:
  {saturated(w, Nat.mul(val(a), val(b)), val(f(a, b)), C.fits(w, Nat.mul(val(a), val(b)))) == True{} : Bool}

def SaturatingPow.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> T, +w: Nat, +a: T, +e: U32) -> Type:
  {saturated(w, Nat.pow(val(a), U32.to_nat(e)), val(f(a, e)), C.fits(w, Nat.pow(val(a), U32.to_nat(e)))) == True{} : Bool}

# ---- overflowing ----

def OverflowingAdd.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +w: Nat, +a: T, +b: T) -> Type:
  {ov_val(~T, ~val, f(a, b)) == C.low(w, Nat.add(val(a), val(b))) : Nat}

def OverflowingAdd.flag(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +w: Nat, +a: T, +b: T) -> Type:
  {ov_flag(T, f(a, b)) == Bool.not(C.fits(w, Nat.add(val(a), val(b)))) : Bool}

def OverflowingSub.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +w: Nat, +a: T, +b: T) -> Type:
  {Nat.add(ov_val(~T, ~val, f(a, b)), val(b)) == Nat.add(val(a), C.shift(w, bn(Nat.is_lt(val(a), val(b))))) : Nat}

def OverflowingSub.flag(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +a: T, +b: T) -> Type:
  {ov_flag(T, f(a, b)) == Nat.is_lt(val(a), val(b)) : Bool}

def OverflowingMul.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +w: Nat, +a: T, +b: T) -> Type:
  {ov_val(~T, ~val, f(a, b)) == C.low(w, Nat.mul(val(a), val(b))) : Nat}

def OverflowingMul.flag(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: T -> F.Over<T>, +w: Nat, +a: T, +b: T) -> Type:
  {ov_flag(T, f(a, b)) == Bool.not(C.fits(w, Nat.mul(val(a), val(b)))) : Bool}

def OverflowingPow.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +w: Nat, +a: T, +e: U32) -> Type:
  {ov_val(~T, ~val, f(a, e)) == C.low(w, Nat.pow(val(a), U32.to_nat(e))) : Nat}

def OverflowingPow.flag(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +w: Nat, +a: T, +e: U32) -> Type:
  {ov_flag(T, f(a, e)) == Bool.not(C.fits(w, Nat.pow(val(a), U32.to_nat(e)))) : Bool}

def OverflowingShl.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +w: Nat, +a: T, +s: U32) -> Type:
  {ov_val(~T, ~val, f(a, s)) == C.low(w, C.shift(Nat.mod(U32.to_nat(s), w), val(a))) : Nat}

def OverflowingShl.flag(~T: Data, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +a: T, +s: U32, +w: Nat) -> Type:
  {ov_flag(T, f(a, s)) == Bool.not(Nat.is_lt(U32.to_nat(s), w)) : Bool}

def OverflowingShr.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +w: Nat, +a: T, +s: U32) -> Type:
  {ov_val(~T, ~val, f(a, s)) == C.high(Nat.mod(U32.to_nat(s), w), val(a)) : Nat}

def OverflowingShr.flag(~T: Data, ~f: @+x: T -> @+y: U32 -> F.Over<T>, +a: T, +s: U32, +w: Nat) -> Type:
  {ov_flag(T, f(a, s)) == Bool.not(Nat.is_lt(U32.to_nat(s), w)) : Bool}

# ---- bit count, primality ----

def BitCount.value(~T: Data, ~val: T -> Nat, ~f: @+x: T -> Nat, +w: Nat, +a: T) -> Type:
  {f(a) == SN.ones(w, val(a)) : Nat}

def IsPrime.value(+a: U32) -> Type:
  {F.u32_is_prime(a) == SN.prime(U32.to_nat(a)) : Bool}

# no prime m with lo <= m < lo + k
def no_prime(k: Nat, +lo: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.not(SN.prime(lo)), no_prime(p, 1n+lo))

# a found p is a prime above n, and none lies strictly between them
def NextPrime.found(+n: U32, +p: U32, +h: {F.u32_next_prime(n) == Some{p} : Maybe<&2, U32>}) -> Type:
  {Bool.and(Bool.and(Nat.is_lt(U32.to_nat(n), U32.to_nat(p)), SN.prime(U32.to_nat(p))), no_prime(Nat.sub(U32.to_nat(p), 1n+U32.to_nat(n)), 1n+U32.to_nat(n))) == True{} : Bool}

# None: no prime m with n < m < 2^32
def NextPrime.none(+n: U32, +h: {F.u32_next_prime(n) == None{} : Maybe<&2, U32>}, +m: Nat, +hm: {Nat.is_lt(U32.to_nat(n), m) == True{} : Bool}, +hf: {C.fits(32n, m) == True{} : Bool}) -> Type:
  {SN.prime(m) == False{} : Bool}

# ---- bytes ----

def nats(xs: List<&2, U32>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.to_nat(x), nats(t)}

# the k lowest base-256 digits of n, least significant first
def le_digits(k: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{C.low(8n, n), le_digits(p, C.high(8n, n))}

def ToBytes.le(~T: Data, ~val: T -> Nat, ~f: @+x: T -> List<&2, U32>, +nb: Nat, +a: T) -> Type:
  {nats(f(a)) == le_digits(nb, val(a)) : List<&2, Nat>}

def ToBytes.be(~T: Data, ~val: T -> Nat, ~f: @+x: T -> List<&2, U32>, +nb: Nat, +a: T) -> Type:
  {nats(f(a)) == C.reverse(Nat, le_digits(nb, val(a))) : List<&2, Nat>}

# the value of exactly k base-256 digits, least significant first; None
# for another length or a digit of 256 or more
def digit_on(r: Maybe<&2, Nat>, ok: Bool, +x: Nat) -> Maybe<&2, Nat>:
  match r:
    case Some{+v}:
      match ok:
        case True{}:
          Some{Nat.add(x, C.shift(8n, v))}
        case False{}:
          None{}
    case None{}:
      None{}

def from_le(k: Nat, xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match k xs:
    case 0n Nil{}:
      Some{0n}
    case 1n+p Con{+x, t}:
      digit_on(from_le(p, t), C.fits(8n, x), x)
    case _ _:
      None{}

def FromBytes.le(~T: Data, ~val: T -> Nat, ~f: List<&2, U32> -> Maybe<&2, T>, +nb: Nat, bs: List<&2, U32>) -> Type:
  {mval(~T, ~val, f(bs)) == from_le(nb, nats(bs)) : Maybe<&2, Nat>}

def FromBytes.be(~T: Data, ~val: T -> Nat, ~f: List<&2, U32> -> Maybe<&2, T>, +nb: Nat, bs: List<&2, U32>) -> Type:
  {mval(~T, ~val, f(bs)) == from_le(nb, C.reverse(Nat, nats(bs))) : Maybe<&2, Nat>}
