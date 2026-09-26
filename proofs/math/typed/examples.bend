import Base
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/instances.bend as SI
import ../../../src/math/instances.bend as I

# Concrete instances of spec/math/generic.bend's integer clauses at U32,
# checked by the proof checker (each normalises both sides). The typed
# functions are not proved; these check that the stated clauses are the
# right statements (argument order, error mapping, ties, zeros) on small
# inputs, next to tools/check_generic.py's randomised tests. Larger values
# and U64 are beyond what the checker evaluates in reasonable time, and
# isqrt (an F32 estimate: Base's float primitives do not evaluate in the
# checker) has none.

def gcd() -> SG.Gcd.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 12, 18):
  {==}

def gcd_zero() -> SG.Gcd.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 0, 7):
  {==}

def lcm() -> SG.Lcm.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 4, 6):
  {==}

def lcm_zero() -> SG.Lcm.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 0, 6):
  {==}

def gcd_all() -> SG.GcdAll.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, Con{12, Con{18, Con{8, Nil{}}}}):
  {==}

def gcd_all_empty() -> SG.GcdAll.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, Nil{}):
  {==}

def lcm_all() -> SG.LcmAll.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, Con{2, Con{3, Con{4, Nil{}}}}):
  {==}

def lcm_all_zero() -> SG.LcmAll.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, Con{2, Con{0, Con{3, Nil{}}}}):
  {==}

def iroot() -> SG.Iroot.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 27, 3n):
  {==}

def iroot_zero_degree() -> SG.Iroot.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 27, 0n):
  {==}

def ilog() -> SG.Ilog.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 100, 10):
  {==}

def ilog_zero() -> SG.Ilog.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 0, 10):
  {==}

def ilog_base_one() -> SG.Ilog.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 100, 1):
  {==}

def factorial() -> SG.Factorial.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 5):
  {==}

def factorial_zero() -> SG.Factorial.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 0):
  {==}

def perm() -> SG.Perm.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 5, 2):
  {==}

def perm_over() -> SG.Perm.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 2, 5):
  {==}

def comb() -> SG.Comb.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 6, 3):
  {==}

def comb_over() -> SG.Comb.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 3, 6):
  {==}

def pow_mod() -> SG.PowMod.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 3, 4, 5):
  {==}

def pow_mod_zero_modulus() -> SG.PowMod.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 3, 4, 0):
  {==}

def mod_inverse() -> SG.ModInverse.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 3, 7):
  {==}

def mod_inverse_not_coprime() -> SG.ModInverse.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 2, 4):
  {==}

def mod_inverse_zero_modulus() -> SG.ModInverse.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 3, 0):
  {==}

def divmod() -> SG.DivMod.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 17, 5):
  {==}

def divmod_zero() -> SG.DivMod.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 17, 0):
  {==}

def bit_length() -> SG.BitLength.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 255):
  {==}

def bit_length_zero() -> SG.BitLength.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 0):
  {==}

def clamp() -> SG.Clamp.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 5, 1, 3):
  {==}

def clamp_domain() -> SG.Clamp.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 5, 3, 1):
  {==}

def min() -> SG.Min.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 2, 5):
  {==}

def min_tie() -> SG.Min.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 3, 3):
  {==}

def max() -> SG.Max.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 2, 5):
  {==}

def abs() -> SG.Abs.identity(~U32, ~I.u32_op, ~I.u32_is, 7):
  {==}

def sign() -> SG.Sign.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 9):
  {==}

def sign_zero() -> SG.Sign.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 0):
  {==}

def sum() -> SG.Sum.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, Con{1, Con{2, Con{3, Nil{}}}}):
  {==}

def prod() -> SG.Prod.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, Con{2, Con{3, Con{0, Nil{}}}}):
  {==}

def pow() -> SG.Pow.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 3, 4n):
  {==}

def pow_zero() -> SG.Pow.checked(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, 32n, 0, 0n):
  {==}

# the instance laws of spec/math/instances.bend at U32 (Sqrt is F32-based: none)

def op_zero() -> SI.Ops.zero(~U32, ~I.u32_op, ~SG.u32_val):
  {==}

def op_one() -> SI.Ops.one(~U32, ~I.u32_op, ~SG.u32_val):
  {==}

def op_add() -> SI.Ops.add(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 7, 9, {==}):
  {==}

def test_add_over() -> SI.Tests.add_over(~U32, ~I.u32_is, ~SG.u32_val, 32n, 7, 9):
  {==}

def op_sub() -> SI.Ops.sub(~U32, ~I.u32_op, ~SG.u32_val, 9, 7, {==}):
  {==}

def op_mul() -> SI.Ops.mul(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, 7, 9, {==}):
  {==}

def test_mul_over() -> SI.Tests.mul_over(~U32, ~I.u32_is, ~SG.u32_val, 32n, 7, 9):
  {==}

def op_quot() -> SI.Ops.quot(~U32, ~I.u32_op, ~SG.u32_val, 17, 5, {==}):
  {==}

def op_rem() -> SI.Ops.rem(~U32, ~I.u32_op, ~SG.u32_val, 17, 5, {==}):
  {==}

def op_half() -> SI.Ops.half(~U32, ~I.u32_op, ~SG.u32_val, 17):
  {==}

def op_mulmod() -> SI.Ops.mulmod(~U32, ~I.u32_op, ~SG.u32_val, 5, 6, 7, {==}, {==}):
  {==}

def op_pow2() -> SI.Ops.pow2(~U32, ~I.u32_op, ~SG.u32_val, 32n, 5n, {==}):
  {==}

def op_abs() -> SI.Ops.abs(~U32, ~I.u32_op, 7):
  {==}

def test_lt() -> SI.Tests.lt(~U32, ~I.u32_is, ~SG.u32_val, 3, 5):
  {==}

def test_odd() -> SI.Tests.odd(~U32, ~I.u32_is, ~SG.u32_val, 7):
  {==}

def test_is_zero() -> SI.Tests.is_zero(~U32, ~I.u32_is, ~SG.u32_val, 0):
  {==}
