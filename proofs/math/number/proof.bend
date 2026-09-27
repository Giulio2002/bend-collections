import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/number.bend as SN
import ../../../spec/math/fixed.bend as SF
import ../../../src/math/u64.bend as WU
import ../../../src/math/fixed.bend as F
import ./egcd.bend as EG
import ./bitcount.bend as BC
import ./prime.bend as PR
import ./fixprime.bend as FP
import ../typed/fix32.bend as P32
import ../typed/fix64.bend as P64
import ../typed/fixbits.bend as FBI
import ../typed/fixbytes.bend as FBY

# Gate for src/math/number.bend and src/math/fixed.bend: every clause of
# spec/math/number.bend and spec/math/fixed.bend, under the clause's name,
# at U32 (width 32) and U64 (width 64). None assumes a hole or an axiom.
#
#   spec/math/number.bend  BitCount.value, Egcd.gcd, Egcd.bezout, IsPrime.value
#   spec/math/fixed.bend   the checked_ / wrapping_ / saturating_ /
#                          overflowing_ families, bit_count, to_bytes /
#                          from_bytes (both widths); is_prime, next_prime (U32)

# ---- Nat ----

def bit_count(+n: Nat) -> SN.BitCount.value(n):
  BC.bit_count_value(n)

def egcd_gcd(+a: Nat, +b: Nat) -> SN.Egcd.gcd(a, b):
  EG.egcd_gcd(a, b)

def egcd_bezout(+a: Nat, +b: Nat) -> SN.Egcd.bezout(a, b):
  EG.egcd_bezout(a, b)

def is_prime(+n: Nat) -> SN.IsPrime.value(n):
  PR.is_prime_value(n)

# ---- u32 ----

def u32_checked_add(+a: U32, +b: U32) -> SF.CheckedAdd.value(~U32, ~SG.u32_val, ~F.u32_checked_add, 32n, a, b):
  P32.checked_add(a, b)

def u32_checked_sub(+a: U32, +b: U32) -> SF.CheckedSub.value(~U32, ~SG.u32_val, ~F.u32_checked_sub, a, b):
  P32.checked_sub(a, b)

def u32_checked_mul(+a: U32, +b: U32) -> SF.CheckedMul.value(~U32, ~SG.u32_val, ~F.u32_checked_mul, 32n, a, b):
  P32.checked_mul(a, b)

def u32_checked_div(+a: U32, +b: U32) -> SF.CheckedDiv.value(~U32, ~SG.u32_val, ~F.u32_checked_div, a, b):
  P32.checked_div(a, b)

def u32_checked_rem(+a: U32, +b: U32) -> SF.CheckedRem.value(~U32, ~SG.u32_val, ~F.u32_checked_rem, a, b):
  P32.checked_rem(a, b)

def u32_checked_pow(+a: U32, +e: U32) -> SF.CheckedPow.value(~U32, ~SG.u32_val, ~F.u32_checked_pow, 32n, a, e):
  P32.checked_pow(a, e)

def u32_checked_shl(+a: U32, +s: U32) -> SF.CheckedShl.value(~U32, ~SG.u32_val, ~F.u32_checked_shl, 32n, a, s):
  P32.checked_shl(a, s)

def u32_checked_shr(+a: U32, +s: U32) -> SF.CheckedShr.value(~U32, ~SG.u32_val, ~F.u32_checked_shr, 32n, a, s):
  P32.checked_shr(a, s)

def u32_wrapping_add(+a: U32, +b: U32) -> SF.WrappingAdd.value(~U32, ~SG.u32_val, ~F.u32_wrapping_add, 32n, a, b):
  P32.wrapping_add(a, b)

def u32_wrapping_sub(+a: U32, +b: U32) -> SF.WrappingSub.value(~U32, ~SG.u32_val, ~F.u32_wrapping_sub, 32n, a, b):
  P32.wrapping_sub(a, b)

def u32_wrapping_mul(+a: U32, +b: U32) -> SF.WrappingMul.value(~U32, ~SG.u32_val, ~F.u32_wrapping_mul, 32n, a, b):
  P32.wrapping_mul(a, b)

def u32_wrapping_pow(+a: U32, +e: U32) -> SF.WrappingPow.value(~U32, ~SG.u32_val, ~F.u32_wrapping_pow, 32n, a, e):
  P32.wrapping_pow(a, e)

def u32_wrapping_shl(+a: U32, +s: U32) -> SF.WrappingShl.value(~U32, ~SG.u32_val, ~F.u32_wrapping_shl, 32n, a, s):
  P32.wrapping_shl(a, s)

def u32_wrapping_shr(+a: U32, +s: U32) -> SF.WrappingShr.value(~U32, ~SG.u32_val, ~F.u32_wrapping_shr, 32n, a, s):
  P32.wrapping_shr(a, s)

def u32_saturating_add(+a: U32, +b: U32) -> SF.SaturatingAdd.value(~U32, ~SG.u32_val, ~F.u32_saturating_add, 32n, a, b):
  P32.saturating_add(a, b)

def u32_saturating_sub(+a: U32, +b: U32) -> SF.SaturatingSub.value(~U32, ~SG.u32_val, ~F.u32_saturating_sub, a, b):
  P32.saturating_sub(a, b)

def u32_saturating_mul(+a: U32, +b: U32) -> SF.SaturatingMul.value(~U32, ~SG.u32_val, ~F.u32_saturating_mul, 32n, a, b):
  P32.saturating_mul(a, b)

def u32_saturating_pow(+a: U32, +e: U32) -> SF.SaturatingPow.value(~U32, ~SG.u32_val, ~F.u32_saturating_pow, 32n, a, e):
  P32.saturating_pow(a, e)

def u32_overflowing_add_value(+a: U32, +b: U32) -> SF.OverflowingAdd.value(~U32, ~SG.u32_val, ~F.u32_overflowing_add, 32n, a, b):
  P32.overflowing_add_value(a, b)

def u32_overflowing_add_flag(+a: U32, +b: U32) -> SF.OverflowingAdd.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_add, 32n, a, b):
  P32.overflowing_add_flag(a, b)

def u32_overflowing_sub_value(+a: U32, +b: U32) -> SF.OverflowingSub.value(~U32, ~SG.u32_val, ~F.u32_overflowing_sub, 32n, a, b):
  P32.overflowing_sub_value(a, b)

def u32_overflowing_sub_flag(+a: U32, +b: U32) -> SF.OverflowingSub.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_sub, a, b):
  P32.overflowing_sub_flag(a, b)

def u32_overflowing_mul_value(+a: U32, +b: U32) -> SF.OverflowingMul.value(~U32, ~SG.u32_val, ~F.u32_overflowing_mul, 32n, a, b):
  P32.overflowing_mul_value(a, b)

def u32_overflowing_mul_flag(+a: U32, +b: U32) -> SF.OverflowingMul.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_mul, 32n, a, b):
  P32.overflowing_mul_flag(a, b)

def u32_overflowing_pow_value(+a: U32, +e: U32) -> SF.OverflowingPow.value(~U32, ~SG.u32_val, ~F.u32_overflowing_pow, 32n, a, e):
  P32.overflowing_pow_value(a, e)

def u32_overflowing_pow_flag(+a: U32, +e: U32) -> SF.OverflowingPow.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_pow, 32n, a, e):
  P32.overflowing_pow_flag(a, e)

def u32_overflowing_shl_value(+a: U32, +s: U32) -> SF.OverflowingShl.value(~U32, ~SG.u32_val, ~F.u32_overflowing_shl, 32n, a, s):
  P32.overflowing_shl_value(a, s)

def u32_overflowing_shl_flag(+a: U32, +s: U32) -> SF.OverflowingShl.flag(~U32, ~F.u32_overflowing_shl, a, s, 32n):
  P32.overflowing_shl_flag(a, s)

def u32_overflowing_shr_value(+a: U32, +s: U32) -> SF.OverflowingShr.value(~U32, ~SG.u32_val, ~F.u32_overflowing_shr, 32n, a, s):
  P32.overflowing_shr_value(a, s)

def u32_overflowing_shr_flag(+a: U32, +s: U32) -> SF.OverflowingShr.flag(~U32, ~F.u32_overflowing_shr, a, s, 32n):
  P32.overflowing_shr_flag(a, s)

def u32_bit_count(+a: U32) -> SF.BitCount.value(~U32, ~SG.u32_val, ~F.u32_bit_count, 32n, a):
  FBI.u32_bit_count(a)

def u32_to_bytes_le(+a: U32) -> SF.ToBytes.le(~U32, ~SG.u32_val, ~F.u32_to_bytes_le, 4n, a):
  FBY.u32_to_le(a)

def u32_to_bytes_be(+a: U32) -> SF.ToBytes.be(~U32, ~SG.u32_val, ~F.u32_to_bytes_be, 4n, a):
  FBY.u32_to_be(a)

def u32_from_bytes_le(bs: List<&2, U32>) -> SF.FromBytes.le(~U32, ~SG.u32_val, ~F.u32_from_bytes_le, 4n, bs):
  FBY.u32_from_le(bs)

def u32_from_bytes_be(bs: List<&2, U32>) -> SF.FromBytes.be(~U32, ~SG.u32_val, ~F.u32_from_bytes_be, 4n, bs):
  FBY.u32_from_be(bs)

def u32_is_prime(+a: U32) -> SF.IsPrime.value(a):
  FP.is_prime(a)

def u32_next_prime_found(+n: U32, +p: U32, +h: {F.u32_next_prime(n) == Some{p} : Maybe<&2, U32>}) -> SF.NextPrime.found(n, p, h):
  FP.found(n, p, h)

def u32_next_prime_none(+n: U32, +h: {F.u32_next_prime(n) == None{} : Maybe<&2, U32>}, +m: Nat, +hm: {Nat.is_lt(U32.to_nat(n), m) == True{} : Bool}, +hf: {C.fits(32n, m) == True{} : Bool}) -> SF.NextPrime.none(n, h, m, hm, hf):
  FP.none(n, h, m, hm, hf)

# ---- u64 ----

def u64_checked_add(+a: WU.U64, +b: WU.U64) -> SF.CheckedAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_add, 64n, a, b):
  P64.checked_add(a, b)

def u64_checked_sub(+a: WU.U64, +b: WU.U64) -> SF.CheckedSub.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_sub, a, b):
  P64.checked_sub(a, b)

def u64_checked_mul(+a: WU.U64, +b: WU.U64) -> SF.CheckedMul.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_mul, 64n, a, b):
  P64.checked_mul(a, b)

def u64_checked_div(+a: WU.U64, +b: WU.U64) -> SF.CheckedDiv.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_div, a, b):
  P64.checked_div(a, b)

def u64_checked_rem(+a: WU.U64, +b: WU.U64) -> SF.CheckedRem.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_rem, a, b):
  P64.checked_rem(a, b)

def u64_checked_pow(+a: WU.U64, +e: U32) -> SF.CheckedPow.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_pow, 64n, a, e):
  P64.checked_pow(a, e)

def u64_checked_shl(+a: WU.U64, +s: U32) -> SF.CheckedShl.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_shl, 64n, a, s):
  P64.checked_shl(a, s)

def u64_checked_shr(+a: WU.U64, +s: U32) -> SF.CheckedShr.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_shr, 64n, a, s):
  P64.checked_shr(a, s)

def u64_wrapping_add(+a: WU.U64, +b: WU.U64) -> SF.WrappingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_add, 64n, a, b):
  P64.wrapping_add(a, b)

def u64_wrapping_sub(+a: WU.U64, +b: WU.U64) -> SF.WrappingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_sub, 64n, a, b):
  P64.wrapping_sub(a, b)

def u64_wrapping_mul(+a: WU.U64, +b: WU.U64) -> SF.WrappingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_mul, 64n, a, b):
  P64.wrapping_mul(a, b)

def u64_wrapping_pow(+a: WU.U64, +e: U32) -> SF.WrappingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_pow, 64n, a, e):
  P64.wrapping_pow(a, e)

def u64_wrapping_shl(+a: WU.U64, +s: U32) -> SF.WrappingShl.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_shl, 64n, a, s):
  P64.wrapping_shl(a, s)

def u64_wrapping_shr(+a: WU.U64, +s: U32) -> SF.WrappingShr.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_shr, 64n, a, s):
  P64.wrapping_shr(a, s)

def u64_saturating_add(+a: WU.U64, +b: WU.U64) -> SF.SaturatingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_add, 64n, a, b):
  P64.saturating_add(a, b)

def u64_saturating_sub(+a: WU.U64, +b: WU.U64) -> SF.SaturatingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_sub, a, b):
  P64.saturating_sub(a, b)

def u64_saturating_mul(+a: WU.U64, +b: WU.U64) -> SF.SaturatingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_mul, 64n, a, b):
  P64.saturating_mul(a, b)

def u64_saturating_pow(+a: WU.U64, +e: U32) -> SF.SaturatingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_pow, 64n, a, e):
  P64.saturating_pow(a, e)

def u64_overflowing_add_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_add, 64n, a, b):
  P64.overflowing_add_value(a, b)

def u64_overflowing_add_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingAdd.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_add, 64n, a, b):
  P64.overflowing_add_flag(a, b)

def u64_overflowing_sub_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_sub, 64n, a, b):
  P64.overflowing_sub_value(a, b)

def u64_overflowing_sub_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingSub.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_sub, a, b):
  P64.overflowing_sub_flag(a, b)

def u64_overflowing_mul_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_mul, 64n, a, b):
  P64.overflowing_mul_value(a, b)

def u64_overflowing_mul_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingMul.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_mul, 64n, a, b):
  P64.overflowing_mul_flag(a, b)

def u64_overflowing_pow_value(+a: WU.U64, +e: U32) -> SF.OverflowingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_pow, 64n, a, e):
  P64.overflowing_pow_value(a, e)

def u64_overflowing_pow_flag(+a: WU.U64, +e: U32) -> SF.OverflowingPow.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_pow, 64n, a, e):
  P64.overflowing_pow_flag(a, e)

def u64_overflowing_shl_value(+a: WU.U64, +s: U32) -> SF.OverflowingShl.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_shl, 64n, a, s):
  P64.overflowing_shl_value(a, s)

def u64_overflowing_shl_flag(+a: WU.U64, +s: U32) -> SF.OverflowingShl.flag(~WU.U64, ~F.u64_overflowing_shl, a, s, 64n):
  P64.overflowing_shl_flag(a, s)

def u64_overflowing_shr_value(+a: WU.U64, +s: U32) -> SF.OverflowingShr.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_shr, 64n, a, s):
  P64.overflowing_shr_value(a, s)

def u64_overflowing_shr_flag(+a: WU.U64, +s: U32) -> SF.OverflowingShr.flag(~WU.U64, ~F.u64_overflowing_shr, a, s, 64n):
  P64.overflowing_shr_flag(a, s)

def u64_bit_count(+a: WU.U64) -> SF.BitCount.value(~WU.U64, ~SG.u64_val, ~F.u64_bit_count, 64n, a):
  FBI.u64_bit_count(a)

def u64_to_bytes_le(+a: WU.U64) -> SF.ToBytes.le(~WU.U64, ~SG.u64_val, ~F.u64_to_bytes_le, 8n, a):
  FBY.u64_to_le(a)

def u64_to_bytes_be(+a: WU.U64) -> SF.ToBytes.be(~WU.U64, ~SG.u64_val, ~F.u64_to_bytes_be, 8n, a):
  FBY.u64_to_be(a)

def u64_from_bytes_le(bs: List<&2, U32>) -> SF.FromBytes.le(~WU.U64, ~SG.u64_val, ~F.u64_from_bytes_le, 8n, bs):
  FBY.u64_from_le(bs)

def u64_from_bytes_be(bs: List<&2, U32>) -> SF.FromBytes.be(~WU.U64, ~SG.u64_val, ~F.u64_from_bytes_be, 8n, bs):
  FBY.u64_from_be(bs)
