import Base
import ./u64.bend as W

# Fast unsigned 64-bit arithmetic on the two-limb U64 of u64.bend, for the U64
# instance of the generic math. Only native U32 operations and Nat values
# below 2^48 (the runtime's Nat bound) are used:
#
#   mul32(a, b)        the full 64-bit product of two U32, by 16-bit halves
#   div32(a, d)        a / d and a mod d for a 64-bit a and a U32 d > 0, the
#                      low word by two 16-bit digits (partial dividends < 2^48)
#   divmod(a, b)       64 / 64: for b >= 2^32 the quotient has 32 bits and is
#                      estimated from the top 32 bits of b (never under and
#                      at most 2 over, Knuth's Theorem B), then corrected down
#   mulmod(a, b, m)    a * b mod m for a, b < m: the 128-bit product reduced
#                      twice by the same estimate
#   isqrt(n)           an F32 estimate, one Newton step, then correction
#
# Tested against Python's integers (tools/check_generic.py); not proved.

def lo(a: W.U64) -> U32:
  match a:
    case W.U64{l, h}:
      l

def hi(a: W.U64) -> U32:
  match a:
    case W.U64{l, h}:
      h

def b32(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def mk(+l: U32, +h: U32) -> W.U64:
  W.U64{l, h}

def of32(+x: U32) -> W.U64:
  W.U64{x, 0}

def is_zero(+a: W.U64) -> Bool:
  Bool.and(U32.is_zero(lo(a)), U32.is_zero(hi(a)))

def lt(+a: W.U64, +b: W.U64) -> Bool:
  Bool.or(U32.is_lt(hi(a), hi(b)), Bool.and(U32.is_eq(hi(a), hi(b)), U32.is_lt(lo(a), lo(b))))

def le(+a: W.U64, +b: W.U64) -> Bool:
  Bool.not(lt(b, a))

def eq(+a: W.U64, +b: W.U64) -> Bool:
  Bool.and(U32.is_eq(lo(a), lo(b)), U32.is_eq(hi(a), hi(b)))

# ---- addition and subtraction (wrapping) ----

def add_fin(+l: U32, +al: U32, +ah: U32, +bh: U32) -> W.U64:
  W.U64{l, U32.add(U32.add(ah, bh), b32(U32.is_lt(l, al)))}

def add(+a: W.U64, +b: W.U64) -> W.U64:
  add_fin(U32.add(lo(a), lo(b)), lo(a), hi(a), hi(b))

def add_over_fin(+s: U32, +ah: U32, c: Bool) -> Bool:
  Bool.or(U32.is_lt(s, ah), Bool.and(c, U32.is_eq(s, 4294967295)))

# a + b >= 2^64
def add_over(+a: W.U64, +b: W.U64) -> Bool:
  add_over_fin(U32.add(hi(a), hi(b)), hi(a), U32.is_lt(U32.add(lo(a), lo(b)), lo(a)))

# a - b mod 2^64
def sub(+a: W.U64, +b: W.U64) -> W.U64:
  W.U64{U32.sub(lo(a), lo(b)), U32.sub(U32.sub(hi(a), hi(b)), b32(U32.is_lt(lo(a), lo(b))))}

def half(+a: W.U64) -> W.U64:
  W.U64{U32.add(U32.shr(lo(a)), U32.mul(U32.and(hi(a), 1), 2147483648)), U32.shr(hi(a))}

def odd(+a: W.U64) -> Bool:
  U32.is_eq(U32.and(lo(a), 1), 1)

# ---- products ----

def mul32_fin(+ll: U32, +mid: U32, +hh: U32, mc: Bool) -> W.U64:
  add_fin(U32.add(ll, U32.mul(mid, 65536)), ll, hh, U32.add(U32.shrn(mid, 16n), U32.mul(b32(mc), 65536)))

def mul32_mid(+ll: U32, +lh: U32, +hl: U32, +hh: U32) -> W.U64:
  mul32_fin(ll, U32.add(lh, hl), hh, U32.is_lt(U32.add(lh, hl), lh))

def mul32_h(+al: U32, +ah: U32, +bl: U32, +bh: U32) -> W.U64:
  mul32_mid(U32.mul(al, bl), U32.mul(al, bh), U32.mul(ah, bl), U32.mul(ah, bh))

# the full product of two U32
def mul32(+a: U32, +b: U32) -> W.U64:
  mul32_h(U32.and(a, 65535), U32.shrn(a, 16n), U32.and(b, 65535), U32.shrn(b, 16n))

# a * b mod 2^64
def mul(+a: W.U64, +b: W.U64) -> W.U64:
  add(mul32(lo(a), lo(b)), W.U64{0, U32.add(U32.mul(lo(a), hi(b)), U32.mul(hi(a), lo(b)))})

def mul_over_one(+p: W.U64, +c: W.U64) -> Bool:
  Bool.or(Bool.not(U32.is_zero(hi(c))), U32.is_lt(U32.add(hi(p), lo(c)), hi(p)))

# a * b >= 2^64
def mul_over(+a: W.U64, +b: W.U64) -> Bool:
  Bool.or(Bool.and(Bool.not(U32.is_zero(hi(a))), Bool.not(U32.is_zero(hi(b)))), mul_over_one(mul32(lo(a), lo(b)), add(mul32(hi(a), lo(b)), mul32(lo(a), hi(b)))))

# ---- 64 / 32 ----

# One digit of the long division by d: (r * base + g) / d and mod d, for a
# remainder r < d < 2^32 and a digit g < base = 2^16, so every partial
# dividend r * 2^16 + g is below 2^48 (the runtime's Nat bound). The low word
# is taken as two 16-bit digits; the base is written 256 * 256 so the proof
# checker never expands a 17-bit literal.
def dig_t(+r: Nat, +base: Nat, +g: Nat) -> Nat:
  Nat.add(Nat.mul(r, base), g)

def dig1(+lo: U32) -> Nat:
  U32.to_nat(U32.shrn(lo, 16n))

def dig2(+lo: U32) -> Nat:
  U32.to_nat(U32.and(lo, 65535))

def div32_fin(+qh: U32, +q1: Nat, +t2: Nat, +d: Nat) -> W.U64 & U32:
  (W.U64{U32.from_nat(Nat.add(Nat.mul(q1, Nat.mul(256n, 256n)), Nat.div(t2, d))), qh}, U32.from_nat(Nat.mod(t2, d)))

def div32_t1(+qh: U32, +lo: U32, +t1: Nat, +d: Nat) -> W.U64 & U32:
  div32_fin(qh, Nat.div(t1, d), dig_t(Nat.mod(t1, d), Nat.mul(256n, 256n), dig2(lo)), d)

# (a / d, a mod d) for d > 0: the high word natively, the low word by digits
def div32(+a: W.U64, +d: U32) -> W.U64 & U32:
  div32_t1(U32.div(hi(a), d), lo(a), dig_t(U32.to_nat(U32.mod(hi(a), d)), Nat.mul(256n, 256n), dig1(lo(a))), U32.to_nat(d))

def mod_step(+r: Nat, +base: Nat, +g: Nat, +d: Nat) -> Nat:
  Nat.mod(dig_t(r, base, g), d)

# a mod d for d > 0
def mod32(+a: W.U64, +d: U32) -> U32:
  U32.from_nat(mod_step(mod_step(U32.to_nat(U32.mod(hi(a), d)), Nat.mul(256n, 256n), dig1(lo(a)), U32.to_nat(d)), Nat.mul(256n, 256n), dig2(lo(a)), U32.to_nat(d)))

# ---- shifts by a variable count ----

# 2^k for k < 32
def pow2(k: Nat) -> U32:
  match k:
    case 0n:
      1
    case 1n:
      2
    case 2n:
      4
    case 3n:
      8
    case 4n:
      16
    case 5n:
      32
    case 6n:
      64
    case 7n:
      128
    case 8n:
      256
    case 9n:
      512
    case 10n:
      1024
    case 11n:
      2048
    case 12n:
      4096
    case 13n:
      8192
    case 14n:
      16384
    case 15n:
      32768
    case 16n:
      65536
    case 17n:
      131072
    case 18n:
      262144
    case 19n:
      524288
    case 20n:
      1048576
    case 21n:
      2097152
    case 22n:
      4194304
    case 23n:
      8388608
    case 24n:
      16777216
    case 25n:
      33554432
    case 26n:
      67108864
    case 27n:
      134217728
    case 28n:
      268435456
    case 29n:
      536870912
    case 30n:
      1073741824
    case _:
      2147483648

def bl_pick(+x: U32, +t: U32, +k: Nat, +base: Nat, big: Bool) -> Nat & U32:
  match big:
    case True{}:
      (Nat.add(base, k), U32.shrn(x, k))
    case False{}:
      (base, x)

def bl_step(+k: Nat, st: Nat & U32) -> Nat & U32:
  (+base, +x) = st
  bl_pick(x, pow2(k), k, base, U32.is_le(pow2(k), x))

def bl_fin(st: Nat & U32) -> Nat:
  (+base, +x) = st
  Nat.add(base, U32.to_nat(U32.min(x, 1)))

# the number of bits of x (0 for 0), by a binary search on the top bit
def bitlen(+x: U32) -> Nat:
  bl_fin(bl_step(1n, bl_step(2n, bl_step(4n, bl_step(8n, bl_step(16n, (0n, x)))))))

def shl_lt(+a: W.U64, +k: Nat) -> W.U64:
  match k:
    case 0n:
      a
    case 1n+ +j:
      W.U64{U32.mul(lo(a), pow2(1n+j)), U32.add(U32.mul(hi(a), pow2(1n+j)), U32.shrn(lo(a), Nat.sub(32n, 1n+j)))}

def shl_ge(+a: W.U64, +k: Nat) -> W.U64:
  W.U64{0, U32.mul(lo(a), pow2(Nat.sub(k, 32n)))}

def shl_pick(+a: W.U64, +k: Nat, small: Bool) -> W.U64:
  match small:
    case True{}:
      shl_lt(a, k)
    case False{}:
      shl_ge(a, k)

# a << k mod 2^64 for k < 64
def shl(+a: W.U64, +k: Nat) -> W.U64:
  shl_pick(a, k, Nat.is_lt(k, 32n))

def shr_lt(+a: W.U64, +k: Nat) -> W.U64:
  match k:
    case 0n:
      a
    case 1n+ +j:
      W.U64{U32.add(U32.shrn(lo(a), 1n+j), U32.mul(hi(a), pow2(Nat.sub(32n, 1n+j)))), U32.shrn(hi(a), 1n+j)}

def shr_ge(+a: W.U64, +k: Nat, huge: Bool) -> W.U64:
  match huge:
    case True{}:
      W.U64{0, 0}
    case False{}:
      W.U64{U32.shrn(hi(a), Nat.sub(k, 32n)), 0}

def shr_pick(+a: W.U64, +k: Nat, small: Bool) -> W.U64:
  match small:
    case True{}:
      shr_lt(a, k)
    case False{}:
      shr_ge(a, k, Nat.is_le(64n, k))

# a >> k (0 for k >= 64)
def shr(+a: W.U64, +k: Nat) -> W.U64:
  shr_pick(a, k, Nat.is_lt(k, 32n))

def fst_q(p: W.U64 & U32) -> W.U64:
  (q, r) = p
  q

def snd_r(p: W.U64 & U32) -> U32:
  (q, r) = p
  r

def q_clamp_z(+l: U32, z: Bool) -> U32:
  match z:
    case True{}:
      l
    case False{}:
      4294967295

# min(q, 2^32 - 1)
def q_clamp(+q: W.U64) -> U32:
  q_clamp_z(lo(q), U32.is_zero(hi(q)))

# the product of a U32 and a U64 as (low 64 bits, top 32 bits)
def mul_32_64_fin(+p0: W.U64, +p1: W.U64) -> W.U64 & U32:
  (W.U64{lo(p0), U32.add(hi(p0), lo(p1))}, U32.add(hi(p1), b32(U32.is_lt(U32.add(hi(p0), lo(p1)), hi(p0)))))

def mul_32_64(+q: U32, +b: W.U64) -> W.U64 & U32:
  mul_32_64_fin(mul32(q, lo(b)), mul32(q, hi(b)))

# the 96-bit product p exceeds x = xh * 2^64 + xl
def over96(+xl: W.U64, +xh: U32, p: W.U64 & U32) -> Bool:
  (+pl, +ph) = p
  Bool.or(U32.is_lt(xh, ph), Bool.and(U32.is_eq(xh, ph), lt(xl, pl)))

# q - 1 while q * b > x: at most q steps (fuel q + 1)
# Loop fuel one above a U32 count. Written Nat.add(..., 1n): the released
# Bend 2.0.28 compiler evaluates 1n+U32.to_nat(x) in 32-bit arithmetic, so
# at x = 2^32 - 1 it wraps to 0 and the loop never runs
# (docs/bend-miscompile-1n-plus.md).
def fuel(+x: U32) -> Nat:
  Nat.add(U32.to_nat(x), 1n)

def q_fix(fuel: Nat, +xl: W.U64, +xh: U32, +b: W.U64, +q: U32, over: Bool) -> U32:
  match fuel over:
    case 0n _:
      q
    case 1n+f False{}:
      q
    case 1n+f True{}:
      q_fix(f, xl, xh, b, U32.sub(q, 1), over96(xl, xh, mul_32_64(U32.sub(q, 1), b)))

# floor(x / b) from an estimate q >= floor(x / b): down while q * b > x (at
# most q steps, fuel q + 1)
def q_start(+xl: W.U64, +xh: U32, +b: W.U64, +q: U32) -> U32:
  q_fix(Nat.add(U32.to_nat(q), 1n), xl, xh, b, q, over96(xl, xh, mul_32_64(q, b)))

# Knuth's estimate for x = xh * 2^64 + xl < b * 2^32 and b >= 2^32, t =
# bits(hi(b)): with Y = x >> t (below 2^64) and B = b >> t in [2^31, 2^32),
# min(floor(Y / B), 2^32 - 1) is at least floor(x / b) (as B 2^t <= b) and at
# most 2 over it (Theorem B), so q_start takes a step or two
def est_lo(+q1: Nat, +t2: Nat, +d: Nat) -> U32:
  U32.from_nat(Nat.add(Nat.mul(q1, Nat.mul(256n, 256n)), Nat.div(t2, d)))

def est_mid(+lo: U32, +t1: Nat, +d: Nat) -> U32:
  est_lo(Nat.div(t1, d), dig_t(Nat.mod(t1, d), Nat.mul(256n, 256n), dig2(lo)), d)

# min(floor(y / d), 2^32 - 1) for d > 0: when hi(y) >= d the quotient needs
# more than 32 bits; otherwise the high word is its own remainder, and div32's
# two 16-bit Nat digit steps finish the division without dividing the high
# word.
def est_pick(+y: W.U64, +d: U32, big: Bool) -> U32:
  match big:
    case True{}:
      4294967295
    case False{}:
      est_mid(lo(y), dig_t(U32.to_nat(hi(y)), Nat.mul(256n, 256n), dig1(lo(y))), U32.to_nat(d))

def est32(+y: W.U64, +d: U32) -> U32:
  est_pick(y, d, U32.is_le(d, hi(y)))

def q_est(+xl: W.U64, +xh: U32, +b: W.U64, +t: Nat) -> U32:
  est32(add(shr(xl, t), shl(W.U64{xh, 0}, Nat.sub(64n, t))), lo(shr(b, t)))

# floor(x / b) for x = xh * 2^64 + xl < b * 2^32 and b >= 2^32, t = bits(hi(b))
def q96(+xl: W.U64, +xh: U32, +b: W.U64, +t: Nat) -> U32:
  q_start(xl, xh, b, q_est(xl, xh, b, t))

# ---- 64 / 64 ----

def dm_small(p: W.U64 & U32) -> W.U64 & W.U64:
  (+q, +r) = p
  (q, W.U64{r, 0})

def dm_big(+a: W.U64, +b: W.U64, +q: U32) -> W.U64 & W.U64:
  (W.U64{q, 0}, sub(a, fst_q(mul_32_64(q, b))))

def dm_pick(+a: W.U64, +b: W.U64, small: Bool) -> W.U64 & W.U64:
  match small:
    case True{}:
      dm_small(div32(a, lo(b)))
    case False{}:
      dm_big(a, b, q96(a, 0, b, bitlen(hi(b))))

# (a / b, a mod b) for b > 0
def divmod(+a: W.U64, +b: W.U64) -> W.U64 & W.U64:
  dm_pick(a, b, U32.is_zero(hi(b)))

def pfst(p: W.U64 & W.U64) -> W.U64:
  (q, r) = p
  q

def psnd(p: W.U64 & W.U64) -> W.U64:
  (q, r) = p
  r

def quot(+a: W.U64, +b: W.U64) -> W.U64:
  pfst(divmod(a, b))

def rem(+a: W.U64, +b: W.U64) -> W.U64:
  psnd(divmod(a, b))

# ---- a * b mod m ----

# x mod m for x = xh * 2^32 + x0 with xh < m and m >= 2^32
def red96_z(+xh: W.U64, +x0: U32, +m: W.U64, small: Bool) -> W.U64:
  match small:
    case True{}:
      W.U64{x0, lo(xh)}
    case False{}:
      sub(W.U64{x0, lo(xh)}, fst_q(mul_32_64(q96(W.U64{x0, lo(xh)}, hi(xh), m, bitlen(hi(m))), m)))

# (the zero test of hi(m) only guards the digit: red96 is called with
# hi(m) != 0; it also stops the proof checker from expanding the digit in
# every statement that names red96)
def red96(+xh: W.U64, +x0: U32, +m: W.U64) -> W.U64:
  red96_z(xh, x0, m, U32.is_zero(hi(m)))

def mul128_fin(+p00: W.U64, +mid: W.U64, c1: Bool, +p11: W.U64) -> W.U64 & W.U64:
  (W.U64{lo(p00), U32.add(hi(p00), lo(mid))}, add(add(p11, W.U64{hi(mid), b32(c1)}), W.U64{b32(U32.is_lt(U32.add(hi(p00), lo(mid)), hi(p00))), 0}))

def mul128_mid(+p00: W.U64, +p01: W.U64, +p10: W.U64, +p11: W.U64) -> W.U64 & W.U64:
  mul128_fin(p00, add(p01, p10), add_over(p01, p10), p11)

# the full product as (low 64 bits, high 64 bits)
def mul128(+a: W.U64, +b: W.U64) -> W.U64 & W.U64:
  mul128_mid(mul32(lo(a), lo(b)), mul32(lo(a), hi(b)), mul32(hi(a), lo(b)), mul32(hi(a), hi(b)))

def mm_big(+m: W.U64, p: W.U64 & W.U64) -> W.U64:
  (+pl, +ph) = p
  red96(red96(ph, hi(pl), m), lo(pl), m)

def mm_pick(+a: W.U64, +b: W.U64, +m: W.U64, small: Bool) -> W.U64:
  match small:
    case True{}:
      W.U64{mod32(mul32(lo(a), lo(b)), lo(m)), 0}
    case False{}:
      mm_big(m, mul128(a, b))

# a * b mod m for a, b < m
def mulmod(+a: W.U64, +b: W.U64, +m: W.U64) -> W.U64:
  mm_pick(a, b, m, U32.is_zero(hi(m)))

# ---- integer square root ----

# r - 1 while r * r > x: from r <= 65535 at most r steps (fuel r + 1), and
# r * r never wraps
def down32(fuel: Nat, +x: U32, +r: U32, over: Bool) -> U32:
  match fuel over:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      down32(f, x, U32.sub(r, 1), U32.is_lt(x, U32.mul(U32.sub(r, 1), U32.sub(r, 1))))

def up_ok(+x: U32, +r: U32) -> Bool:
  Bool.and(U32.is_lt(r, 65535), U32.is_le(U32.mul(U32.add(r, 1), U32.add(r, 1)), x))

# r + 1 while r < 65535 and (r + 1)^2 <= x: at most 65535 - r steps
def up32(fuel: Nat, +x: U32, +r: U32, up: Bool) -> U32:
  match fuel up:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      up32(f, x, U32.add(r, 1), up_ok(x, U32.add(r, 1)))

def isqrt32_fix(+x: U32, +r: U32) -> U32:
  up32(fuel(U32.sub(65535, r)), x, r, up_ok(x, r))

# floor(sqrt(x)) from any estimate r <= 65535: down while r^2 > x, then up
# while (r + 1)^2 <= x. The F32 square root lands within 1, so both loops
# take at most a step or two; the fuel covers any estimate, so the result
# never depends on F32's accuracy.
def isqrt32_est(+x: U32, +r: U32) -> U32:
  isqrt32_fix(x, down32(fuel(r), x, r, U32.is_lt(x, U32.mul(r, r))))

def isqrt32(+x: U32) -> U32:
  isqrt32_est(x, U32.min(F32.to_u32(F32.sqrt(U32.to_f32(x))), 65535))

def sq_over(+n: W.U64, +r: U32) -> Bool:
  lt(n, mul32(r, r))

def down64(fuel: Nat, +n: W.U64, +r: U32, over: Bool) -> U32:
  match fuel over:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      down64(f, n, U32.sub(r, 1), sq_over(n, U32.sub(r, 1)))

def up64_ok(+n: W.U64, +r: U32) -> Bool:
  Bool.and(U32.is_lt(r, 4294967295), Bool.not(sq_over(n, U32.add(r, 1))))

def up64(fuel: Nat, +n: W.U64, +r: U32, up: Bool) -> U32:
  match fuel up:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      up64(f, n, U32.add(r, 1), up64_ok(n, U32.add(r, 1)))

def isqrt64_fix(+n: W.U64, +r: U32) -> U32:
  up64(fuel(U32.sub(4294967295, r)), n, r, up64_ok(n, r))

# floor(sqrt(n)) from any estimate r1: down while r^2 > n, then up while
# (r + 1)^2 <= n; the fuel covers any estimate
def isqrt_newton(+n: W.U64, +r1: U32) -> U32:
  isqrt64_fix(n, down64(fuel(r1), n, r1, sq_over(n, r1)))

# one Newton step from the F32 estimate r0 > 0 lands within a few units of
# floor(sqrt(n)); the correction makes the result exact for any r0
def isqrt_big(+n: W.U64, +r0: U32) -> W.U64:
  W.U64{isqrt_newton(n, q_clamp(half(add(fst_q(div32(n, r0)), W.U64{r0, 0})))), 0}

def f32_clamp32(+f: F32, big: Bool) -> U32:
  match big:
    case True{}:
      4294967295
    case False{}:
      F32.to_u32(f)

def isqrt_est(+f: F32) -> U32:
  U32.max(f32_clamp32(f, F32.is_le(4294967040.0, f)), 1)

def isqrt_pick(+n: W.U64, small: Bool) -> W.U64:
  match small:
    case True{}:
      W.U64{isqrt32(lo(n)), 0}
    case False{}:
      isqrt_big(n, isqrt_est(F32.sqrt(F32.add(F32.mul(U32.to_f32(hi(n)), 4294967296.0), U32.to_f32(lo(n))))))

def isqrt(+n: W.U64) -> W.U64:
  isqrt_pick(n, U32.is_zero(hi(n)))

def w_pow2(+k: Nat, small: Bool) -> W.U64:
  match small:
    case True{}:
      W.U64{pow2(k), 0}
    case False{}:
      W.U64{0, pow2(Nat.sub(k, 32n))}

# ---- general shifts and leading zeros (the software F64) ----

def or_bit(+a: W.U64, b: Bool) -> W.U64:
  W.U64{U32.or(lo(a), b32(b)), hi(a)}

def jam_pick(+a: W.U64, +k: Nat, huge: Bool) -> W.U64:
  match huge:
    case True{}:
      W.U64{b32(Bool.not(is_zero(a))), 0}
    case False{}:
      or_bit(shr(a, k), Bool.not(eq(shl(shr(a, k), k), a)))

# a >> k with the bits shifted out OR-ed into bit 0 (SoftFloat's
# shiftRightJam64)
def shr_jam(+a: W.U64, +k: Nat) -> W.U64:
  jam_pick(a, k, Nat.is_le(64n, k))

def clz_pick(+a: W.U64, high: Bool) -> Nat:
  match high:
    case True{}:
      Nat.sub(32n, bitlen(hi(a)))
    case False{}:
      Nat.sub(64n, bitlen(lo(a)))

# the number of leading zero bits of a (64 for 0)
def clz(+a: W.U64) -> Nat:
  clz_pick(a, Bool.not(U32.is_zero(hi(a))))

# a with bit 0 cleared when b
def clear0(+a: W.U64, b: Bool) -> W.U64:
  W.U64{U32.sub(lo(a), U32.and(lo(a), b32(b))), hi(a)}

def cmp_pick(less: Bool, same: Bool) -> Cmp:
  match less same:
    case True{} _:
      LT{}
    case False{} True{}:
      EQ{}
    case False{} False{}:
      GT{}

def cmp(+a: W.U64, +b: W.U64) -> Cmp:
  cmp_pick(lt(a, b), eq(a, b))

# ---- Montgomery multiplication (odd m, 2^32 <= m < 2^63, R = 2^64) ----
# REDC (Montgomery 1985; the word-level algorithm HACL* and Fiat Crypto
# verify): for t < m^2 and mp = -1/m mod 2^64, u = t mp mod 2^64 makes
# t + u m divisible by 2^64, and r = (t + u m) / 2^64 < 2 m is t / 2^64 mod m
# after one conditional subtraction.

# x (2 - m x): doubles the correct low bits of an inverse of m mod 2^64
def inv_step(+m: W.U64, +x: W.U64) -> W.U64:
  mul(x, sub(W.U64{2, 0}, mul(m, x)))

# -1 / m mod 2^64 for odd m (m is its own inverse mod 8; five Newton steps
# reach 96 >= 64 bits)
def minv(+m: W.U64) -> W.U64:
  sub(W.U64{0, 0}, inv_step(m, inv_step(m, inv_step(m, inv_step(m, inv_step(m, m))))))

def sub_if(+r: W.U64, +m: W.U64, big: Bool) -> W.U64:
  match big:
    case True{}:
      sub(r, m)
    case False{}:
      r

def redc_r(+m: W.U64, +r: W.U64) -> W.U64:
  sub_if(r, m, le(m, r))

def redc_p(+m: W.U64, +tl: W.U64, +th: W.U64, p: W.U64 & W.U64) -> W.U64:
  (+pl, +ph) = p
  redc_r(m, add(add(th, ph), W.U64{b32(add_over(tl, pl)), 0}))

# t / 2^64 mod m for t = (tl, th) < m^2
def redc(+m: W.U64, +mp: W.U64, t: W.U64 & W.U64) -> W.U64:
  (+tl, +th) = t
  redc_p(m, tl, th, mul128(mul(tl, mp), m))

# a b / 2^64 mod m for a, b < m
def mont(+m: W.U64, +mp: W.U64, +a: W.U64, +b: W.U64) -> W.U64:
  redc(m, mp, mul128(a, b))

def mbit(odd: Bool, +m: W.U64, +mp: W.U64, +b: W.U64, +acc: W.U64) -> W.U64:
  match odd:
    case False{}:
      acc
    case True{}:
      mont(m, mp, acc, b)

# pow_mod_go of generic.bend on Montgomery forms x 2^64 mod m
def mpow_go(fuel: Nat, +m: W.U64, +mp: W.U64, +b: W.U64, +acc: W.U64, st: W.U64 & Bool) -> W.U64:
  match fuel st:
    case 0n _:
      acc
    case 1n+f Tuple{e, True{}}:
      acc
    case 1n+f Tuple{+e, False{}}:
      mpow_go(f, m, mp, mont(m, mp, b, b), mbit(odd(e), m, mp, b, acc), (half(e), is_zero(half(e))))

# x 2^64 mod m for x < m, m >= 2^32
def to_mont(+x: W.U64, +m: W.U64) -> W.U64:
  red96(red96(x, 0, m), 0, m)

# m odd with 2^32 <= m < 2^63 and m minv(m) = -1 mod 2^64 (always so for odd
# m; checked, so the proof needs no Hensel lemma)
def mont_ok(+m: W.U64) -> Bool:
  Bool.and(Bool.and(odd(m), eq(mul(m, minv(m)), W.U64{4294967295, 4294967295})), Bool.and(Bool.not(U32.is_zero(hi(m))), U32.is_lt(hi(m), 2147483648)))

def mpow_m(+b: W.U64, +e: W.U64, +m: W.U64, +mp: W.U64) -> W.U64:
  mont(m, mp, mpow_go(140n, m, mp, to_mont(b, m), to_mont(rem(W.U64{1, 0}, m), m), (e, is_zero(e))), W.U64{1, 0})

# b^e mod m for b < m and mont_ok(m)
def mpow(+b: W.U64, +e: W.U64, +m: W.U64) -> W.U64:
  mpow_m(b, e, m, minv(m))

# ---- 32-bit Montgomery multiplication (odd m, R = 2^32) ----

def inv32_step(+m: U32, +x: U32) -> U32:
  U32.mul(x, U32.sub(2, U32.mul(m, x)))

# -1 / m mod 2^32 for odd m
def minv32(+m: U32) -> U32:
  U32.sub(0, inv32_step(m, inv32_step(m, inv32_step(m, inv32_step(m, m)))))

def sub_if32(+r: W.U64, +m: U32, big: Bool) -> U32:
  match big:
    case True{}:
      lo(sub(r, W.U64{m, 0}))
    case False{}:
      lo(r)

def redc32_r(+m: U32, +r: W.U64) -> U32:
  sub_if32(r, m, le(W.U64{m, 0}, r))

def redc32_s(+m: U32, +s1: U32, +s2: U32, +c1: Bool) -> U32:
  redc32_r(m, W.U64{s2, U32.add(b32(c1), b32(U32.is_lt(s2, s1)))})

def redc32_p(+m: U32, +t: W.U64, +p: W.U64) -> U32:
  redc32_s(m, U32.add(hi(t), hi(p)), U32.add(U32.add(hi(t), hi(p)), b32(U32.is_lt(U32.add(lo(t), lo(p)), lo(t)))), U32.is_lt(U32.add(hi(t), hi(p)), hi(t)))

def redc32(+m: U32, +mp: U32, +t: W.U64) -> U32:
  redc32_p(m, t, mul32(U32.mul(lo(t), mp), m))

def mont32(+m: U32, +mp: U32, +a: U32, +b: U32) -> U32:
  redc32(m, mp, mul32(a, b))

def mbit32(odd: Bool, +m: U32, +mp: U32, +b: U32, +acc: U32) -> U32:
  match odd:
    case False{}:
      acc
    case True{}:
      mont32(m, mp, acc, b)

def mpow32_go(fuel: Nat, +m: U32, +mp: U32, +b: U32, +acc: U32, st: U32 & Bool) -> U32:
  match fuel st:
    case 0n _:
      acc
    case 1n+f Tuple{e, True{}}:
      acc
    case 1n+f Tuple{+e, False{}}:
      mpow32_go(f, m, mp, mont32(m, mp, b, b), mbit32(U32.is_eq(U32.and(e, 1), 1), m, mp, b, acc), (U32.shr(e), U32.is_zero(U32.shr(e))))

def mont32_ok(+m: U32) -> Bool:
  Bool.and(U32.is_eq(U32.and(m, 1), 1), U32.is_eq(U32.mul(m, minv32(m)), 4294967295))

def mpow32_m(+b: U32, +e: U32, +m: U32, +mp: U32) -> U32:
  mont32(m, mp, mpow32_go(140n, m, mp, mod32(W.U64{0, b}, m), mod32(W.U64{0, U32.mod(1, m)}, m), (e, U32.is_zero(e))), 1)

def mpow32(+b: U32, +e: U32, +m: U32) -> U32:
  mpow32_m(b, e, m, minv32(m))

# a and b fit 48 bits (runtime Nats) and a has more than 16: the binary gcd
# then hands them to Euclid on Nat (native division); below 2^16 its few
# steps are cheaper
def small2(+a: W.U64, +b: W.U64) -> Bool:
  Bool.and(Bool.and(U32.is_lt(hi(a), 65536), U32.is_lt(hi(b), 65536)), Bool.or(Bool.not(U32.is_zero(hi(a))), U32.is_lt(65535, lo(a))))

def n48(+a: W.U64) -> Nat:
  Nat.add(U32.to_nat(lo(a)), Nat.mul(Nat.mul(U32.to_nat(hi(a)), Nat.mul(256n, 256n)), Nat.mul(256n, 256n)))

def of48(+g: Nat) -> W.U64:
  W.U64{U32.from_nat(Nat.mod(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))), U32.from_nat(Nat.div(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))))}
