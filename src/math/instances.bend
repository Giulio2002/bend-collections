import Base
import ./num.bend as N
import ./u64.bend as W
import ./w64.bend as X

# Numeric instances for generic.bend (num.bend's Op and Test per type):
# U32 (Base), U64 (the two-limb U64 of u64.bend, fast arithmetic in
# w64.bend) and F32 (Base's float); F64 lives in f64.bend.
#
#   G.gcd(~U32, ~I.u32_op, ~I.u32_is, a, b)
#   G.gcd(~W.U64, ~I.u64_op, ~I.u64_is, a, b)
#   G.pow(~F32, ~I.f32_op, ~I.f32_is, x, k)
#
# Fixed widths are checked: generic.bend forms Add and Mul only next to their
# over-test and uses the result only if the test says it fits.

# ---- U32 ----

# a * b >= 2^32: the full product has a nonzero high word
def u32_mul_over(+a: U32, +b: U32) -> Bool:
  Bool.not(U32.is_zero(X.hi(X.mul32(a, b))))

def u32_mulmod(+a: U32, +b: U32, +m: U32) -> U32:
  X.mod32(X.mul32(a, b), m)

def u32_op(o: N.Op<U32>) -> U32:
  match o:
    case N.ZeroOp{}:
      0
    case N.One{}:
      1
    case N.Add{a, b}:
      U32.add(a, b)
    case N.Sub{a, b}:
      U32.sub(a, b)
    case N.Mul{a, b}:
      U32.mul(a, b)
    case N.Neg{a}:
      U32.sub(0, a)
    case N.Abs{a}:
      a
    case N.Quot{a, b}:
      U32.div(a, b)
    case N.Rem{a, b}:
      U32.mod(a, b)
    case N.Half{a}:
      U32.shr(a)
    case N.MulMod{a, b, m}:
      u32_mulmod(a, b, m)
    case N.Pow2{k}:
      X.pow2(k)
    case N.Sqrt{a}:
      X.isqrt32(a)

def u32_add_over(+a: U32, +b: U32) -> Bool:
  U32.is_lt(U32.add(a, b), a)

def u32_odd(+a: U32) -> Bool:
  U32.is_eq(U32.and(a, 1), 1)

def u32_is(t: N.Test<U32>) -> Bool:
  match t:
    case N.Lt{a, b}:
      U32.is_lt(a, b)
    case N.AddOver{a, b}:
      u32_add_over(a, b)
    case N.MulOver{a, b}:
      u32_mul_over(a, b)
    case N.Odd{a}:
      u32_odd(a)
    case N.IsZero{a}:
      U32.is_zero(a)

# ---- U64 ----

# 2^k for k < 64
def u64_pow2(+k: Nat) -> W.U64:
  X.w_pow2(k, Nat.is_lt(k, 32n))

def u64_op(o: N.Op<W.U64>) -> W.U64:
  match o:
    case N.ZeroOp{}:
      W.U64{0, 0}
    case N.One{}:
      W.U64{1, 0}
    case N.Add{a, b}:
      X.add(a, b)
    case N.Sub{a, b}:
      X.sub(a, b)
    case N.Mul{a, b}:
      X.mul(a, b)
    case N.Neg{a}:
      X.sub(W.U64{0, 0}, a)
    case N.Abs{a}:
      a
    case N.Quot{a, b}:
      X.quot(a, b)
    case N.Rem{a, b}:
      X.rem(a, b)
    case N.Half{a}:
      X.half(a)
    case N.MulMod{a, b, m}:
      X.mulmod(a, b, m)
    case N.Pow2{k}:
      u64_pow2(k)
    case N.Sqrt{a}:
      X.isqrt(a)

def u64_is(t: N.Test<W.U64>) -> Bool:
  match t:
    case N.Lt{a, b}:
      X.lt(a, b)
    case N.AddOver{a, b}:
      X.add_over(a, b)
    case N.MulOver{a, b}:
      X.mul_over(a, b)
    case N.Odd{a}:
      X.odd(a)
    case N.IsZero{a}:
      X.is_zero(a)

# ---- F32 ----

def f32_op(o: N.Op<F32>) -> F32:
  match o:
    case N.ZeroOp{}:
      0.0
    case N.One{}:
      1.0
    case N.Add{a, b}:
      F32.add(a, b)
    case N.Sub{a, b}:
      F32.sub(a, b)
    case N.Mul{a, b}:
      F32.mul(a, b)
    case N.Neg{a}:
      F32.neg(a)
    case N.Abs{a}:
      F32.abs(a)
    case N.Quot{a, b}:
      F32.div(a, b)
    case N.Rem{a, b}:
      F32.mod(a, b)
    case N.Half{a}:
      F32.mul(a, 0.5)
    case N.MulMod{a, b, m}:
      F32.mod(F32.mul(a, b), m)
    case N.Pow2{k}:
      F32.pow(2.0, F32.from_nat(k))
    case N.Sqrt{a}:
      F32.sqrt(a)

def f32_is(t: N.Test<F32>) -> Bool:
  match t:
    case N.Lt{a, b}:
      F32.is_lt(a, b)
    case N.AddOver{a, b}:
      False{}
    case N.MulOver{a, b}:
      False{}
    case N.Odd{a}:
      False{}
    case N.IsZero{a}:
      F32.is_eq(a, 0.0)
