import Base
import ./u64.bend as W
import ./w64.bend as X
import ./generic.bend as G
import ./instances.bend as I
import ./number.bend as NB
import ./num.bend as N

# Fixed-width integer operations for U32 and the two-limb U64, as Rust
# defines them for u32/u64 (design reference section 2.6: "provide explicit
# families: checked_add, wrapping_add, saturating_add, overflowing_add"),
# plus bit counts, primality and byte serialisation (sections 3.2, 10).
#
#   checked_{add,sub,mul,div,rem,pow,shl,shr}    Maybe: None on overflow,
#                                                a zero divisor, or a
#                                                shift >= the width
#   wrapping_{add,sub,mul,pow,shl,shr}           modulo 2^width (shifts use
#                                                the amount mod the width)
#   saturating_{add,sub,mul,pow}                 clamped to [0, 2^width - 1]
#   overflowing_{add,sub,mul,pow,shl,shr}        (wrapping result, overflowed)
#   bit_count(x)                                 number of 1 bits
#   is_prime(x), next_prime(x)                   U32: trial division (exact)
#   to_bytes_le/be, from_bytes_le/be             bytes as U32s in [0, 256)
#
# Unsigned division never overflows, so Rust's wrapping_/saturating_/
# overflowing_ div and rem are plain division; checked_div/rem cover the
# zero divisor (Rust panics there; here it is None). Shift amounts and pow
# exponents are U32, as in Rust. Every operation is the Nat operation on
# the values (spec/math/fixed.bend).

type Over<-T: Data> is Data:
  OV{value: T, overflow: Bool}

# ---- shared helpers ----

def opt(-T: Data, bad: Bool, +r: T) -> Maybe<&2, T>:
  match bad:
    case True{}:
      None{}
    case False{}:
      Some{r}

def pick(-T: Data, c: Bool, +a: T, +b: T) -> T:
  match c:
    case True{}:
      a
    case False{}:
      b

def res_opt(-T: Data, r: Result<&2, &2, N.NumError, T>) -> Maybe<&2, T>:
  match r:
    case Done{x}:
      Some{x}
    case Fail{e}:
      None{}

def or_top(-T: Data, +top: T, r: Maybe<&2, T>) -> T:
  match r:
    case Some{x}:
      x
    case None{}:
      top

def res_bad(-T: Data, r: Result<&2, &2, N.NumError, T>) -> Bool:
  match r:
    case Done{x}:
      False{}
    case Fail{e}:
      True{}

# ---- U32 ----

def u32_max() -> U32:
  4294967295

def u32_add_over(+a: U32, +b: U32) -> Bool:
  I.u32_add_over(a, b)

def u32_mul_over(+a: U32, +b: U32) -> Bool:
  I.u32_mul_over(a, b)

def u32_checked_add(+a: U32, +b: U32) -> Maybe<&2, U32>:
  opt(U32, u32_add_over(a, b), U32.add(a, b))

def u32_wrapping_add(+a: U32, +b: U32) -> U32:
  U32.add(a, b)

def u32_saturating_add(+a: U32, +b: U32) -> U32:
  pick(U32, u32_add_over(a, b), u32_max(), U32.add(a, b))

def u32_overflowing_add(+a: U32, +b: U32) -> Over<U32>:
  OV{U32.add(a, b), u32_add_over(a, b)}

def u32_checked_sub(+a: U32, +b: U32) -> Maybe<&2, U32>:
  opt(U32, U32.is_lt(a, b), U32.sub(a, b))

def u32_wrapping_sub(+a: U32, +b: U32) -> U32:
  U32.sub(a, b)

def u32_saturating_sub(+a: U32, +b: U32) -> U32:
  pick(U32, U32.is_lt(a, b), 0, U32.sub(a, b))

def u32_overflowing_sub(+a: U32, +b: U32) -> Over<U32>:
  OV{U32.sub(a, b), U32.is_lt(a, b)}

def u32_checked_mul(+a: U32, +b: U32) -> Maybe<&2, U32>:
  opt(U32, u32_mul_over(a, b), U32.mul(a, b))

def u32_wrapping_mul(+a: U32, +b: U32) -> U32:
  U32.mul(a, b)

def u32_saturating_mul(+a: U32, +b: U32) -> U32:
  pick(U32, u32_mul_over(a, b), u32_max(), U32.mul(a, b))

def u32_overflowing_mul(+a: U32, +b: U32) -> Over<U32>:
  OV{U32.mul(a, b), u32_mul_over(a, b)}

def u32_checked_div(+a: U32, +b: U32) -> Maybe<&2, U32>:
  opt(U32, U32.is_zero(b), U32.div(a, b))

def u32_checked_rem(+a: U32, +b: U32) -> Maybe<&2, U32>:
  opt(U32, U32.is_zero(b), U32.mod(a, b))

def u32_checked_pow(+a: U32, +e: U32) -> Maybe<&2, U32>:
  res_opt(U32, G.pow(~U32, ~I.u32_op, ~I.u32_is, a, U32.to_nat(e)))

# binary exponentiation modulo 2^32; e halves every step (32 steps)
def u32_wpow(fuel: Nat, +e: U32, +b: U32, +acc: U32, z: Bool) -> U32:
  match fuel z:
    case 0n _:
      acc
    case 1n+f True{}:
      acc
    case 1n+ +f False{}:
      u32_wpow(f, U32.shr(e), U32.mul(b, b), pick(U32, I.u32_odd(e), U32.mul(acc, b), acc), U32.is_zero(U32.shr(e)))

def u32_wrapping_pow(+a: U32, +e: U32) -> U32:
  u32_wpow(32n, e, a, 1, U32.is_zero(e))

def u32_saturating_pow(+a: U32, +e: U32) -> U32:
  or_top(U32, u32_max(), u32_checked_pow(a, e))

def u32_overflowing_pow(+a: U32, +e: U32) -> Over<U32>:
  OV{u32_wrapping_pow(a, e), res_bad(U32, G.pow(~U32, ~I.u32_op, ~I.u32_is, a, U32.to_nat(e)))}

# shifts by s mod 32 (Rust masks the amount the same way); a left shift is
# the product with 2^k modulo 2^32
def u32_wrapping_shl(+a: U32, +s: U32) -> U32:
  U32.mul(a, X.pow2(U32.to_nat(U32.and(s, 31))))

def u32_checked_shl(+a: U32, +s: U32) -> Maybe<&2, U32>:
  opt(U32, Bool.not(U32.is_lt(s, 32)), u32_wrapping_shl(a, s))

def u32_overflowing_shl(+a: U32, +s: U32) -> Over<U32>:
  OV{u32_wrapping_shl(a, s), Bool.not(U32.is_lt(s, 32))}

def u32_wrapping_shr(+a: U32, +s: U32) -> U32:
  U32.shrn(a, U32.to_nat(U32.and(s, 31)))

def u32_checked_shr(+a: U32, +s: U32) -> Maybe<&2, U32>:
  opt(U32, Bool.not(U32.is_lt(s, 32)), u32_wrapping_shr(a, s))

def u32_overflowing_shr(+a: U32, +s: U32) -> Over<U32>:
  OV{u32_wrapping_shr(a, s), Bool.not(U32.is_lt(s, 32))}

# ---- bit count ----

# the 1 bits of a value below 16
def ones4(+n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      1n
    case 2n:
      1n
    case 3n:
      2n
    case 4n:
      1n
    case 5n:
      2n
    case 6n:
      2n
    case 7n:
      3n
    case 8n:
      1n
    case 9n:
      2n
    case 10n:
      2n
    case 11n:
      3n
    case 12n:
      2n
    case 13n:
      3n
    case 14n:
      3n
    case 15n:
      4n
    case 16n+m:
      0n

# the 1 bits of the k low nibbles of x, a nibble at a time
def u32_bc_go(fuel: Nat, +x: U32) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+k:
      Nat.add(ones4(U32.to_nat(U32.mod(x, 16))), u32_bc_go(k, U32.shrn(x, 4n)))

def u32_bit_count(+x: U32) -> Nat:
  u32_bc_go(8n, x)

# ---- primality (U32: trial division on the value) ----

def u32_is_prime(+x: U32) -> Bool:
  NB.is_prime(U32.to_nat(x))

# the least prime above n below 2^32: the candidates n+1, n+2, ... stop at
# the first prime or when the next candidate wraps to 0
def u32_np(fuel: Nat, +m: U32, wrapped: Bool, prime: Bool) -> Maybe<&2, U32>:
  match fuel wrapped prime:
    case 0n _ _:
      None{}
    case 1n+f True{} _:
      None{}
    case 1n+f False{} True{}:
      Some{m}
    case 1n+ +f False{} False{}:
      u32_np(f, U32.add(m, 1), U32.is_zero(U32.add(m, 1)), NB.is_prime(U32.to_nat(U32.add(m, 1))))

def u32_next_prime(+n: U32) -> Maybe<&2, U32>:
  u32_np(Nat.add(U32.to_nat(U32.not(n)), 1n), U32.add(n, 1), U32.is_zero(U32.add(n, 1)), NB.is_prime(U32.to_nat(U32.add(n, 1))))

# ---- bytes (U32 values in [0, 256)) ----

def byte32(+x: U32, +k: Nat) -> U32:
  U32.mod(U32.shrn(x, Nat.mul(8n, k)), 256)

def u32_to_bytes_le(+x: U32) -> List<&2, U32>:
  [byte32(x, 0n), byte32(x, 1n), byte32(x, 2n), byte32(x, 3n)]

def u32_to_bytes_be(+x: U32) -> List<&2, U32>:
  [byte32(x, 3n), byte32(x, 2n), byte32(x, 1n), byte32(x, 0n)]

def is_byte(+b: U32) -> Bool:
  U32.is_lt(b, 256)

# one more base-256 digit below the value so far: b + 256 z
def dig32(r: Maybe<&2, U32>, ok: Bool, +b: U32) -> Maybe<&2, U32>:
  match r:
    case Some{+z}:
      match ok:
        case True{}:
          Some{U32.add(b, U32.mul(z, 256))}
        case False{}:
          None{}
    case None{}:
      None{}

def from4(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> Maybe<&2, U32>:
  dig32(dig32(dig32(dig32(Some{0}, is_byte(b3), b3), is_byte(b2), b2), is_byte(b1), b1), is_byte(b0), b0)

def u32_from_bytes_le(bs: List<&2, U32>) -> Maybe<&2, U32>:
  match bs:
    case [+b0, +b1, +b2, +b3]:
      from4(b0, b1, b2, b3)
    case _:
      None{}

def u32_from_bytes_be(bs: List<&2, U32>) -> Maybe<&2, U32>:
  match bs:
    case [+b3, +b2, +b1, +b0]:
      from4(b0, b1, b2, b3)
    case _:
      None{}

# ---- U64 ----

def u64_max() -> W.U64:
  W.U64{4294967295, 4294967295}

def u64_zero() -> W.U64:
  W.U64{0, 0}

def u64_checked_add(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  opt(W.U64, X.add_over(a, b), X.add(a, b))

def u64_wrapping_add(+a: W.U64, +b: W.U64) -> W.U64:
  X.add(a, b)

def u64_saturating_add(+a: W.U64, +b: W.U64) -> W.U64:
  pick(W.U64, X.add_over(a, b), u64_max(), X.add(a, b))

def u64_overflowing_add(+a: W.U64, +b: W.U64) -> Over<W.U64>:
  OV{X.add(a, b), X.add_over(a, b)}

# a - b modulo 2^64 for any a, b: a + (2^64 - 1 - b) + 1
def u64_wsub(+a: W.U64, +b: W.U64) -> W.U64:
  X.add(X.add(a, X.sub(u64_max(), b)), W.U64{1, 0})

def u64_checked_sub(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  opt(W.U64, X.lt(a, b), X.sub(a, b))

def u64_wrapping_sub(+a: W.U64, +b: W.U64) -> W.U64:
  u64_wsub(a, b)

def u64_saturating_sub(+a: W.U64, +b: W.U64) -> W.U64:
  pick(W.U64, X.lt(a, b), u64_zero(), X.sub(a, b))

def u64_overflowing_sub(+a: W.U64, +b: W.U64) -> Over<W.U64>:
  OV{u64_wsub(a, b), X.lt(a, b)}

def u64_checked_mul(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  opt(W.U64, X.mul_over(a, b), X.mul(a, b))

def u64_wrapping_mul(+a: W.U64, +b: W.U64) -> W.U64:
  X.mul(a, b)

def u64_saturating_mul(+a: W.U64, +b: W.U64) -> W.U64:
  pick(W.U64, X.mul_over(a, b), u64_max(), X.mul(a, b))

def u64_overflowing_mul(+a: W.U64, +b: W.U64) -> Over<W.U64>:
  OV{X.mul(a, b), X.mul_over(a, b)}

# the quotient is only computed for a nonzero divisor (the two-limb
# division by zero would build a Nat past the runtime's 2^48 bound)
def u64_cdiv(z: Bool, +a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{X.quot(a, b)}

def u64_crem(z: Bool, +a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{X.rem(a, b)}

def u64_checked_div(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  u64_cdiv(X.is_zero(b), a, b)

def u64_checked_rem(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  u64_crem(X.is_zero(b), a, b)

def u64_checked_pow(+a: W.U64, +e: U32) -> Maybe<&2, W.U64>:
  res_opt(W.U64, G.pow(~W.U64, ~I.u64_op, ~I.u64_is, a, U32.to_nat(e)))

def u64_wpow(fuel: Nat, +e: U32, +b: W.U64, +acc: W.U64, z: Bool) -> W.U64:
  match fuel z:
    case 0n _:
      acc
    case 1n+f True{}:
      acc
    case 1n+ +f False{}:
      u64_wpow(f, U32.shr(e), X.mul(b, b), pick(W.U64, I.u32_odd(e), X.mul(acc, b), acc), U32.is_zero(U32.shr(e)))

def u64_wrapping_pow(+a: W.U64, +e: U32) -> W.U64:
  u64_wpow(32n, e, a, W.U64{1, 0}, U32.is_zero(e))

def u64_saturating_pow(+a: W.U64, +e: U32) -> W.U64:
  or_top(W.U64, u64_max(), u64_checked_pow(a, e))

def u64_overflowing_pow(+a: W.U64, +e: U32) -> Over<W.U64>:
  OV{u64_wrapping_pow(a, e), res_bad(W.U64, G.pow(~W.U64, ~I.u64_op, ~I.u64_is, a, U32.to_nat(e)))}

def u64_checked_shl(+a: W.U64, +s: U32) -> Maybe<&2, W.U64>:
  opt(W.U64, Bool.not(U32.is_lt(s, 64)), X.shl(a, U32.to_nat(U32.and(s, 63))))

def u64_wrapping_shl(+a: W.U64, +s: U32) -> W.U64:
  X.shl(a, U32.to_nat(U32.and(s, 63)))

def u64_overflowing_shl(+a: W.U64, +s: U32) -> Over<W.U64>:
  OV{u64_wrapping_shl(a, s), Bool.not(U32.is_lt(s, 64))}

def u64_checked_shr(+a: W.U64, +s: U32) -> Maybe<&2, W.U64>:
  opt(W.U64, Bool.not(U32.is_lt(s, 64)), X.shr(a, U32.to_nat(U32.and(s, 63))))

def u64_wrapping_shr(+a: W.U64, +s: U32) -> W.U64:
  X.shr(a, U32.to_nat(U32.and(s, 63)))

def u64_overflowing_shr(+a: W.U64, +s: U32) -> Over<W.U64>:
  OV{u64_wrapping_shr(a, s), Bool.not(U32.is_lt(s, 64))}

def u64_bit_count(+x: W.U64) -> Nat:
  Nat.add(u32_bit_count(X.lo(x)), u32_bit_count(X.hi(x)))

def u64_to_bytes_le(+x: W.U64) -> List<&2, U32>:
  [byte32(X.lo(x), 0n), byte32(X.lo(x), 1n), byte32(X.lo(x), 2n), byte32(X.lo(x), 3n), byte32(X.hi(x), 0n), byte32(X.hi(x), 1n), byte32(X.hi(x), 2n), byte32(X.hi(x), 3n)]

def u64_to_bytes_be(+x: W.U64) -> List<&2, U32>:
  [byte32(X.hi(x), 3n), byte32(X.hi(x), 2n), byte32(X.hi(x), 1n), byte32(X.hi(x), 0n), byte32(X.lo(x), 3n), byte32(X.lo(x), 2n), byte32(X.lo(x), 1n), byte32(X.lo(x), 0n)]

def dig64(r: Maybe<&2, W.U64>, ok: Bool, +b: U32) -> Maybe<&2, W.U64>:
  match r:
    case Some{+z}:
      match ok:
        case True{}:
          Some{X.add(W.U64{b, 0}, X.mul(z, W.U64{256, 0}))}
        case False{}:
          None{}
    case None{}:
      None{}

def u64_from_bytes_le(bs: List<&2, U32>) -> Maybe<&2, W.U64>:
  match bs:
    case [+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7]:
      dig64(dig64(dig64(dig64(dig64(dig64(dig64(dig64(Some{W.U64{0, 0}}, is_byte(b7), b7), is_byte(b6), b6), is_byte(b5), b5), is_byte(b4), b4), is_byte(b3), b3), is_byte(b2), b2), is_byte(b1), b1), is_byte(b0), b0)
    case _:
      None{}

def u64_from_bytes_be(bs: List<&2, U32>) -> Maybe<&2, W.U64>:
  match bs:
    case [+b7, +b6, +b5, +b4, +b3, +b2, +b1, +b0]:
      dig64(dig64(dig64(dig64(dig64(dig64(dig64(dig64(Some{W.U64{0, 0}}, is_byte(b7), b7), is_byte(b6), b6), is_byte(b5), b5), is_byte(b4), b4), is_byte(b3), b3), is_byte(b2), b2), is_byte(b1), b1), is_byte(b0), b0)
    case _:
      None{}
