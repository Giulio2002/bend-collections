import Base
import ./num.bend as N
import ./u64.bend as W

# Numeric instances for generic.bend: U32 (Base), U64 (the two-limb U64 of
# u64.bend) and F32 (Base's float), plus F64 in f64.bend. Fixed widths are
# checked: add, sub, mul and neg answer None instead of wrapping. The 64-bit
# words are handled through Nat pieces below 2^48 (the runtime's Nat bound):
# 32-bit halves for adds and compares, 16-bit digits for products.

# ---- U32 ----

# 2^32 (Nat literals stop at 2^32 - 1)
def two32() -> Nat:
  Nat.add(4294967295n, 1n)

def u32_fits(+x: U32, good: Bool) -> Maybe<&2, U32>:
  match good:
    case True{}:
      Some{x}
    case False{}:
      None{}

def u32_add(+a: U32, +b: U32) -> Maybe<&2, U32>:
  u32_fits(U32.add(a, b), Bool.not(U32.is_lt(U32.add(a, b), a)))

def u32_sub(+a: U32, +b: U32) -> Maybe<&2, U32>:
  u32_fits(U32.sub(a, b), Bool.not(U32.is_lt(a, b)))

def u32_mul(+a: U32, +b: U32) -> Maybe<&2, U32>:
  u32_fits(U32.mul(a, b), Bool.or(U32.is_zero(a), U32.is_eq(U32.div(U32.mul(a, b), a), b)))

def u32_neg(+a: U32) -> Maybe<&2, U32>:
  u32_fits(0, U32.is_zero(a))

def u32_divmod(+a: U32, +b: U32) -> U32 & U32:
  (U32.div(a, b), U32.mod(a, b))

def u32_from_nat(+n: Nat) -> Maybe<&2, U32>:
  u32_fits(U32.from_nat(n), Nat.is_lt(n, two32()))

def u32_odd(+a: U32) -> Bool:
  Bool.not(U32.is_even(a))

# a * b mod m for a, b < m < 2^32, in Nat: a * (b / 2^16) < 2^48
def nat_mulmod32(+a: Nat, +b: Nat, +m: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mod(Nat.mul(Nat.mod(Nat.mul(a, Nat.div(b, 65536n)), m), 65536n), m), Nat.mod(Nat.mul(a, Nat.mod(b, 65536n)), m)), m)

def u32_mulmod(+a: U32, +b: U32, +m: U32) -> U32:
  U32.from_nat(nat_mulmod32(U32.to_nat(a), U32.to_nat(b), U32.to_nat(m)))

def u32_id(+a: U32) -> U32:
  a

def u32_arith() -> N.Arith<U32>:
  N.Arith{0, 1, (a => b => u32_add(a, b)), (a => b => u32_sub(a, b)), (a => b => u32_mul(a, b)), (a => u32_neg(a)), (a => b => U32.is_lt(a, b)), (a => u32_id(a))}

def u32() -> N.Integer<U32>:
  N.Integer{u32_arith(), (a => b => u32_divmod(a, b)), (a => u32_from_nat(a)), 32n, (a => U32.shr(a)), (a => u32_odd(a)), (a => b => m => u32_mulmod(a, b, m))}

# ---- U64 ----

def w_lo(+a: W.U64) -> Nat:
  match a:
    case W.U64{lo, hi}:
      U32.to_nat(lo)

def w_hi(+a: W.U64) -> Nat:
  match a:
    case W.U64{lo, hi}:
      U32.to_nat(hi)

# the word hi * 2^32 + lo, for hi, lo < 2^32
def w_make(+lo: Nat, +hi: Nat) -> W.U64:
  W.U64{U32.from_nat(lo), U32.from_nat(hi)}

def w_lt(+a: W.U64, +b: W.U64) -> Bool:
  Bool.or(Nat.is_lt(w_hi(a), w_hi(b)), Bool.and(Nat.is_eq(w_hi(a), w_hi(b)), Nat.is_lt(w_lo(a), w_lo(b))))

def w_fits(+x: W.U64, good: Bool) -> Maybe<&2, W.U64>:
  match good:
    case True{}:
      Some{x}
    case False{}:
      None{}

def w_add_fin(+lo: Nat, +hi: Nat) -> Maybe<&2, W.U64>:
  w_fits(w_make(Nat.mod(lo, two32()), hi), Nat.is_lt(hi, two32()))

def w_add(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  w_add_fin(Nat.add(w_lo(a), w_lo(b)), Nat.add(Nat.add(w_hi(a), w_hi(b)), Nat.div(Nat.add(w_lo(a), w_lo(b)), two32())))

def w_sub_borrow(+a: W.U64, +b: W.U64, borrow: Bool) -> W.U64:
  match borrow:
    case False{}:
      w_make(Nat.sub(w_lo(a), w_lo(b)), Nat.mod(Nat.sub(Nat.add(w_hi(a), two32()), w_hi(b)), two32()))
    case True{}:
      w_make(Nat.sub(Nat.add(w_lo(a), two32()), w_lo(b)), Nat.mod(Nat.sub(Nat.add(w_hi(a), 4294967295n), w_hi(b)), two32()))

# a - b for b <= a (wrapping otherwise, as 2^64 + a - b)
def w_sub_wrap(+a: W.U64, +b: W.U64) -> W.U64:
  w_sub_borrow(a, b, Nat.is_lt(w_lo(a), w_lo(b)))

def w_sub(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  w_fits(w_sub_wrap(a, b), Bool.not(w_lt(a, b)))

def mul32_low(+low: Nat, +mid: Nat, +hh: Nat) -> Nat & Nat:
  (Nat.mod(low, two32()), Nat.add(Nat.add(hh, Nat.div(mid, 65536n)), Nat.div(low, two32())))

# the full product of x, y < 2^32 by 16-bit digits: (low word, high word)
def mul32_fin(+ll: Nat, +mid: Nat, +hh: Nat) -> Nat & Nat:
  mul32_low(Nat.add(ll, Nat.mul(Nat.mod(mid, 65536n), 65536n)), mid, hh)

def mul32(+x: Nat, +y: Nat) -> Nat & Nat:
  mul32_fin(Nat.mul(Nat.mod(x, 65536n), Nat.mod(y, 65536n)), Nat.add(Nat.mul(Nat.div(x, 65536n), Nat.mod(y, 65536n)), Nat.mul(Nat.mod(x, 65536n), Nat.div(y, 65536n))), Nat.mul(Nat.div(x, 65536n), Nat.div(y, 65536n)))

# a * b with at most one high half nonzero: al * bl + 2^32 (ah * bl + al * bh)
def w_mul_fin(p0: Nat & Nat, cross: Nat & Nat) -> Maybe<&2, W.U64>:
  (+l0, +h0) = p0
  (+cl, +ch) = cross
  w_fits(w_make(l0, Nat.mod(Nat.add(h0, cl), two32())), Bool.and(Nat.is_eq(ch, 0n), Nat.is_lt(Nat.add(h0, cl), two32())))

def w_cross(+a: W.U64, +b: W.U64, a_high: Bool) -> Nat & Nat:
  match a_high:
    case True{}:
      mul32(w_hi(a), w_lo(b))
    case False{}:
      mul32(w_lo(a), w_hi(b))

def w_mul_both(+a: W.U64, +b: W.U64, both: Bool) -> Maybe<&2, W.U64>:
  match both:
    case True{}:
      None{}
    case False{}:
      w_mul_fin(mul32(w_lo(a), w_lo(b)), w_cross(a, b, Nat.is_lt(0n, w_hi(a))))

def w_mul(+a: W.U64, +b: W.U64) -> Maybe<&2, W.U64>:
  w_mul_both(a, b, Bool.and(Nat.is_lt(0n, w_hi(a)), Nat.is_lt(0n, w_hi(b))))

def w_neg(+a: W.U64) -> Maybe<&2, W.U64>:
  w_fits(a, Bool.and(Nat.is_eq(w_lo(a), 0n), Nat.is_eq(w_hi(a), 0n)))

def w_is_zero(+a: W.U64) -> Bool:
  Bool.and(Nat.is_eq(w_lo(a), 0n), Nat.is_eq(w_hi(a), 0n))

def w_shr1(+a: W.U64) -> W.U64:
  w_make(Nat.add(Nat.div(w_lo(a), 2n), Nat.mul(Nat.mod(w_hi(a), 2n), 2147483648n)), Nat.div(w_hi(a), 2n))

def w_odd(+a: W.U64) -> Bool:
  Nat.is_eq(Nat.mod(w_lo(a), 2n), 1n)

# bit i of a (i < 64)
# 2x + bit, with the bit shifted out of the top (the carry)
def w_twice_fin(+lo: Nat, +hi: Nat) -> W.U64 & Bool:
  (w_make(Nat.mod(lo, two32()), Nat.mod(Nat.add(hi, Nat.div(lo, two32())), two32())), Nat.is_le(two32(), Nat.add(hi, Nat.div(lo, two32()))))

# 2x + bit for x < 2^63
def w_twice(+x: W.U64, +bit: Nat) -> W.U64 & Bool:
  w_twice_fin(Nat.add(Nat.mul(w_lo(x), 2n), bit), Nat.mul(w_hi(x), 2n))

def w_div_d1(+d: Nat, +a0: Nat, +q3: Nat, +q2: Nat, +q1: Nat, +r: Nat) -> W.U64 & W.U64:
  (w_make(Nat.add(Nat.mul(q1, 65536n), Nat.div(Nat.add(Nat.mul(r, 65536n), a0), d)), Nat.add(Nat.mul(q3, 65536n), q2)), w_make(Nat.mod(Nat.add(Nat.mul(r, 65536n), a0), d), 0n))

def w_div_d2(+d: Nat, +a1: Nat, +a0: Nat, +q3: Nat, +q2: Nat, +r: Nat) -> W.U64 & W.U64:
  w_div_d1(d, a0, q3, q2, Nat.div(Nat.add(Nat.mul(r, 65536n), a1), d), Nat.mod(Nat.add(Nat.mul(r, 65536n), a1), d))

# a / d for d < 2^32 by 16-bit digits: every partial remainder times 2^16
# plus a digit stays below 2^48
def w_div_digits(+d: Nat, +a3: Nat, +a2: Nat, +a1: Nat, +a0: Nat) -> W.U64 & W.U64:
  w_div_d2(d, a1, a0, Nat.div(a3, d), Nat.div(Nat.add(Nat.mul(Nat.mod(a3, d), 65536n), a2), d), Nat.mod(Nat.add(Nat.mul(Nat.mod(a3, d), 65536n), a2), d))

def w_div_small(+a: W.U64, +d: Nat) -> W.U64 & W.U64:
  w_div_digits(d, Nat.div(w_hi(a), 65536n), Nat.mod(w_hi(a), 65536n), Nat.div(w_lo(a), 65536n), Nat.mod(w_lo(a), 65536n))

def w_div_pick(+b: W.U64, +lo: Nat, +q: Nat, +x: W.U64, take: Bool) -> (Nat & (Nat & W.U64)):
  match take:
    case True{}:
      (lo, (Nat.add(Nat.mul(q, 2n), 1n), w_sub_wrap(x, b)))
    case False{}:
      (lo, (Nat.mul(q, 2n), x))

# b >= 2^32: the quotient has 32 bits, so the remainder starts as a >> 32
# and takes the low word's bits one at a time (restoring division; a carry
# out of the top means the true remainder exceeds b)
def w_div_take(+b: W.U64, +lo: Nat, +q: Nat, t: W.U64 & Bool) -> (Nat & (Nat & W.U64)):
  (+x, +carry) = t
  w_div_pick(b, lo, q, x, Bool.or(carry, Bool.not(w_lt(x, b))))

def w_div_step2(+b: W.U64, +lo: Nat, qr: Nat & W.U64) -> (Nat & (Nat & W.U64)):
  (+q, +r) = qr
  w_div_take(b, Nat.mod(Nat.mul(lo, 2n), two32()), q, w_twice(r, Nat.div(lo, 2147483648n)))

def w_div_step(+b: W.U64, st: Nat & (Nat & W.U64)) -> (Nat & (Nat & W.U64)):
  (+lo, qr) = st
  w_div_step2(b, lo, qr)

def w_div_big_go(k: Nat, +b: W.U64, st: Nat & (Nat & W.U64)) -> (Nat & (Nat & W.U64)):
  match k:
    case 0n:
      st
    case 1n+j:
      w_div_big_go(j, b, w_div_step(b, st))

def w_div_big_fin2(qr: Nat & W.U64) -> W.U64 & W.U64:
  (+q, +r) = qr
  (w_make(q, 0n), r)

def w_div_big_fin(st: Nat & (Nat & W.U64)) -> W.U64 & W.U64:
  (lo, qr) = st
  w_div_big_fin2(qr)

def w_divmod_pick(+a: W.U64, +b: W.U64, small: Bool) -> W.U64 & W.U64:
  match small:
    case True{}:
      w_div_small(a, w_lo(b))
    case False{}:
      w_div_big_fin(w_div_big_go(32n, b, (w_lo(a), (0n, w_make(w_hi(a), 0n)))))

def w_divmod(+a: W.U64, +b: W.U64) -> W.U64 & W.U64:
  w_divmod_pick(a, b, Nat.is_eq(w_hi(b), 0n))

def w_from_nat(+n: Nat) -> Maybe<&2, W.U64>:
  Some{w_make(Nat.mod(n, two32()), Nat.div(n, two32()))}

def w_addmod_fin(+x: W.U64, +y: W.U64, +gap: W.U64, below: Bool) -> W.U64:
  match below:
    case True{}:
      w_make(Nat.mod(Nat.add(w_lo(x), w_lo(y)), two32()), Nat.add(Nat.add(w_hi(x), w_hi(y)), Nat.div(Nat.add(w_lo(x), w_lo(y)), two32())))
    case False{}:
      w_sub_wrap(x, gap)

# x + y mod m for x, y < m, never forming a sum above m
def w_addmod(+m: W.U64, +x: W.U64, +y: W.U64) -> W.U64:
  w_addmod_fin(x, y, w_sub_wrap(m, y), w_lt(x, w_sub_wrap(m, y)))

def w_mulmod_bit(+m: W.U64, +x: W.U64, +acc: W.U64, odd: Bool) -> W.U64:
  match odd:
    case True{}:
      w_addmod(m, acc, x)
    case False{}:
      acc

# a * b mod m by doubling over the bits of b (a, b < m)
def w_mulmod_go(k: Nat, +m: W.U64, +b: W.U64, +x: W.U64, +acc: W.U64) -> W.U64:
  match k:
    case 0n:
      acc
    case 1n+j:
      w_mulmod_go(j, m, w_shr1(b), w_addmod(m, x, x), w_mulmod_bit(m, x, acc, w_odd(b)))

def w_mulmod_small(+a: W.U64, +b: W.U64, +m: W.U64, small: Bool) -> W.U64:
  match small:
    case True{}:
      w_make(nat_mulmod32(w_lo(a), w_lo(b), w_lo(m)), 0n)
    case False{}:
      w_mulmod_go(64n, m, b, a, W.U64{0, 0})

def w_mulmod(+a: W.U64, +b: W.U64, +m: W.U64) -> W.U64:
  w_mulmod_small(a, b, m, Nat.is_eq(w_hi(m), 0n))

def w_id(+a: W.U64) -> W.U64:
  a

def u64_arith() -> N.Arith<W.U64>:
  N.Arith{W.U64{0, 0}, W.U64{1, 0}, (a => b => w_add(a, b)), (a => b => w_sub(a, b)), (a => b => w_mul(a, b)), (a => w_neg(a)), (a => b => w_lt(a, b)), (a => w_id(a))}

def u64() -> N.Integer<W.U64>:
  N.Integer{u64_arith(), (a => b => w_divmod(a, b)), (a => w_from_nat(a)), 64n, (a => w_shr1(a)), (a => w_odd(a)), (a => b => m => w_mulmod(a, b, m))}

# ---- F32 ----

def f32_add(+a: F32, +b: F32) -> Maybe<&2, F32>:
  Some{F32.add(a, b)}

def f32_sub(+a: F32, +b: F32) -> Maybe<&2, F32>:
  Some{F32.sub(a, b)}

def f32_mul(+a: F32, +b: F32) -> Maybe<&2, F32>:
  Some{F32.mul(a, b)}

def f32_neg(+a: F32) -> Maybe<&2, F32>:
  Some{F32.neg(a)}

def f32() -> N.Arith<F32>:
  N.Arith{0.0, 1.0, (a => b => f32_add(a, b)), (a => b => f32_sub(a, b)), (a => b => f32_mul(a, b)), (a => f32_neg(a)), (a => b => F32.is_lt(a, b)), (a => F32.abs(a))}
