import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32div.bend as UD
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/lemmas/proofs/word_multiplication.bend as WM
import ../../lib/lemmas/spec/numeric.bend as S
import ../u64/u64div.bend as PD
import ../u64/u64.bend as P64
import ./width.bend as WW

# Mul32.value of spec/math/w64.bend: the full 64-bit product of two U32 by
# 16-bit halves (Knuth TAOCP 4.3.1 algorithm M with 2^16 digits; the same
# decomposition as the verified schoolbook multiplication of Why3's WhyMP,
# Rieu-Helft, Marche & Melquiond, "How to get an efficient yet verified
# arbitrary-precision integer library", VSTTE 2017, and of HACL*'s
# Hacl.Bignum.Multiplication). The digit products fit 32 bits; the middle
# sum carries into the high word; the high word never overflows because the
# product is below 2^64.
#
# 2^k stays WD.sc(k, one) with a symbolic one == 1, so no power of two is
# ever expanded by the checker.

def v(+x: U32) -> Nat:
  UD.v(x)

# ---- small arithmetic ----

def le_mul_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, b), Nat.mul(a, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(a, b), Nat.mul(b, a), NA.mul_comm(a, b)) : {Nat.is_le(_, Nat.mul(a, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(a, c), Nat.mul(c, a), NA.mul_comm(a, c)) : {Nat.is_le(Nat.mul(b, a), _) == True{} : Bool}
  AR.mul_le(b, c, a, h)

# x, y < s gives x * y < s * s
def mul_lt_sq(+x: Nat, +y: Nat, +s: Nat, +hx: {Nat.is_lt(x, s) == True{} : Bool}, +hy: {Nat.is_lt(y, s) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), Nat.mul(s, s)) == True{} : Bool}:
  match s:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(x, y), 0n) == True{} : Bool}, N.lt_zero_absurd(x, hx))
    case 1n+ +sp:
      +a1 = AR.mul_le(x, sp, y, N.lt_succ_le(x, sp, hx))
      +a2 = le_mul_r(sp, y, sp, N.lt_succ_le(y, sp, hy))
      +a3 = le_mul_r(sp, sp, 1n+sp, N.le_succ(sp))
      +a4 = N.le_trans(Nat.mul(x, y), Nat.mul(sp, y), Nat.mul(sp, sp), a1, a2)
      +a5 = N.le_trans(Nat.mul(x, y), Nat.mul(sp, sp), Nat.mul(sp, 1n+sp), a4, a3)
      N.le_lt_trans(Nat.mul(x, y), Nat.mul(sp, 1n+sp), Nat.add(1n+sp, Nat.mul(sp, 1n+sp)), a5, N.lt_add_r2(0n, 1n+sp, Nat.mul(sp, 1n+sp), {==}))

def sq_sc(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(WD.sc(k, one), WD.sc(k, one)) == WD.sc(Nat.add(k, k), one) : Nat}:
  Equal.trans(Nat, Nat.mul(WD.sc(k, one), WD.sc(k, one)), WD.sc(k, WD.sc(k, one)), WD.sc(Nat.add(k, k), one), AR.mul_sc1(k, one, h1, WD.sc(k, one)), Equal.sym(Nat, WD.sc(Nat.add(k, k), one), WD.sc(k, WD.sc(k, one)), AR.sc_idx(k, k, one)))

def mul_sc1(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(x, WD.sc(k, one)) == WD.sc(k, x) : Nat}:
  AR.mul_sc1(k, one, h1, x)

# ---- a U32 in 16-bit halves (c == 2^16, m == 2^16 - 1 kept symbolic) ----

def nz16(+c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}) -> {U32.is_zero(c) == False{} : Bool}:
  L.subst(U32, z => {U32.is_zero(z) == False{} : Bool}, U32{WD.pw(32n, 16n)}, c, Equal.sym(U32, c, U32{WD.pw(32n, 16n)}, pc), {==})

def h16(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}) -> {v(c) == WD.sc(16n, one) : Nat}:
  PD.pow32(16n, {==}, one, h1, c, pc)

def lo16(+x: U32, +m: U32) -> Nat:
  v(U32.and(x, m))

def hi16(+x: U32, +c: U32) -> Nat:
  v(U32.div(x, c))

def lo16_lt(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}) -> {Nat.is_lt(lo16(x, m), WD.sc(16n, one)) == True{} : Bool}:
  PD.and32_lt(16n, one, h1, x, m, pm)

# v(x) == 2^16 hi + (x mod 2^16)
def dm16(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}) -> {Nat.add(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))) == v(x) : Nat}:
  +e = PD.dm_e(x, c, nz16(c, pc))
  %PD.mul_pow(one, h1, 16n, hi16(x, c), v(c), h16(one, h1, c, pc)) : {Nat.add(_, v(U32.mod(x, c))) == v(x) : Nat}
  e

def hi16_lt(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}) -> {Nat.is_lt(hi16(x, c), WD.sc(16n, one)) == True{} : Bool}:
  +le = L.subst(Nat, z => {Nat.is_le(WD.sc(16n, hi16(x, c)), z) == True{} : Bool}, Nat.add(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))), v(x), dm16(one, h1, x, c, pc), N.le_add_right(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))))
  +lt = N.le_lt_trans(WD.sc(16n, hi16(x, c)), v(x), WD.sc(32n, one), le, UD.vb(one, h1, x))
  AR.sc_lt_cancel(16n, hi16(x, c), WD.sc(16n, one), L.subst(Nat, z => {Nat.is_lt(WD.sc(16n, hi16(x, c)), z) == True{} : Bool}, WD.sc(32n, one), WD.sc(16n, WD.sc(16n, one)), AR.sc_idx(16n, 16n, one), lt))

# v(x) == lo + 2^16 hi
def split16(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}) -> {v(x) == Nat.add(lo16(x, m), WD.sc(16n, hi16(x, c))) : Nat}:
  +em = dm16(one, h1, x, c, pc)
  +ea = PD.and32(16n, x, m, pm)
  +bm = L.subst(Nat, z => {Nat.is_lt(v(U32.mod(x, c)), z) == True{} : Bool}, v(c), WD.sc(16n, one), h16(one, h1, c, pc), PD.dm_l(x, c, nz16(c, pc)))
  +ex = Equal.trans(Nat, Nat.add(v(U32.mod(x, c)), WD.sc(16n, hi16(x, c))), v(x), Nat.add(lo16(x, m), WD.sc(16n, PD.hp32(16n, x))), Equal.trans(Nat, Nat.add(v(U32.mod(x, c)), WD.sc(16n, hi16(x, c))), Nat.add(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))), v(x), N.add_comm(v(U32.mod(x, c)), WD.sc(16n, hi16(x, c))), em), ea)
  +er = WD.uniq(16n, one, h1, v(U32.mod(x, c)), lo16(x, m), hi16(x, c), PD.hp32(16n, x), ex, bm, lo16_lt(one, h1, x, m, pm))
  %er : {v(x) == Nat.add(_, WD.sc(16n, hi16(x, c))) : Nat}
  Equal.trans(Nat, v(x), Nat.add(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))), Nat.add(v(U32.mod(x, c)), WD.sc(16n, hi16(x, c))), Equal.sym(Nat, Nat.add(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))), v(x), em), N.add_comm(WD.sc(16n, hi16(x, c)), v(U32.mod(x, c))))

# ---- algebra ----

def cong_l(+x: Nat, +y: Nat, +z: Nat, +e: {x == y : Nat}) -> {Nat.add(x, z) == Nat.add(y, z) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(t, z), x, y, e)

def cong_r(+z: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.add(z, x) == Nat.add(z, y) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(z, t), x, y, e)

def cong_sc(+k: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {WD.sc(k, x) == WD.sc(k, y) : Nat}:
  Equal.cong(Nat, Nat, t => WD.sc(k, t), x, y, e)

# q * 2^k d == 2^k (q d)
def mul_sc_r(+k: Nat, +q: Nat, +d: Nat) -> {Nat.mul(q, WD.sc(k, d)) == WD.sc(k, Nat.mul(q, d)) : Nat}:
  Equal.trans(Nat, Nat.mul(q, WD.sc(k, d)), Nat.mul(WD.sc(k, d), q), WD.sc(k, Nat.mul(q, d)), NA.mul_comm(q, WD.sc(k, d)), Equal.trans(Nat, Nat.mul(WD.sc(k, d), q), WD.sc(k, Nat.mul(d, q)), WD.sc(k, Nat.mul(q, d)), Equal.sym(Nat, WD.sc(k, Nat.mul(d, q)), Nat.mul(WD.sc(k, d), q), AR.sc_mul(k, d, q)), cong_sc(k, Nat.mul(d, q), Nat.mul(q, d), NA.mul_comm(d, q))))

# 2^k q * d == 2^k (q d)
def mul_sc_l(+k: Nat, +q: Nat, +d: Nat) -> {Nat.mul(WD.sc(k, q), d) == WD.sc(k, Nat.mul(q, d)) : Nat}:
  Equal.sym(Nat, WD.sc(k, Nat.mul(q, d)), Nat.mul(WD.sc(k, q), d), AR.sc_mul(k, q, d))

# 2^j (2^k x) == 2^(j+k) x
def sc_sc(+j: Nat, +k: Nat, +x: Nat) -> {WD.sc(j, WD.sc(k, x)) == WD.sc(Nat.add(j, k), x) : Nat}:
  Equal.sym(Nat, WD.sc(Nat.add(j, k), x), WD.sc(j, WD.sc(k, x)), AR.sc_idx(j, k, x))

def sc_add2(+k: Nat, +x: Nat, +y: Nat) -> {WD.sc(k, Nat.add(x, y)) == Nat.add(WD.sc(k, x), WD.sc(k, y)) : Nat}:
  Equal.sym(Nat, Nat.add(WD.sc(k, x), WD.sc(k, y)), WD.sc(k, Nat.add(x, y)), A.sc_add(k, x, y))

# (a + b) + (c + d) == (a + c) + (b + d)
def add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), NA.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), cong_r(a, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), NA.add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), NA.add_assoc(a, c, Nat.add(b, d)))))

# (al + 2^16 ah)(bl + 2^16 bh) == (al bl + 2^16 al bh) + (2^16 ah bl + 2^32 ah bh)
def expand16(+al: Nat, +ah: Nat, +bl: Nat, +bh: Nat) -> {Nat.mul(Nat.add(al, WD.sc(16n, ah)), Nat.add(bl, WD.sc(16n, bh))) == Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))) : Nat}:
  +b = Nat.add(bl, WD.sc(16n, bh))
  +sa = WD.sc(16n, ah)
  +sb = WD.sc(16n, bh)
  +e6 = Equal.trans(Nat, Nat.mul(sa, sb), WD.sc(16n, Nat.mul(ah, sb)), WD.sc(32n, Nat.mul(ah, bh)), mul_sc_l(16n, ah, sb), Equal.trans(Nat, WD.sc(16n, Nat.mul(ah, sb)), WD.sc(16n, WD.sc(16n, Nat.mul(ah, bh))), WD.sc(32n, Nat.mul(ah, bh)), cong_sc(16n, Nat.mul(ah, sb), WD.sc(16n, Nat.mul(ah, bh)), mul_sc_r(16n, ah, bh)), sc_sc(16n, 16n, Nat.mul(ah, bh))))
  +l1 = Nat.add(Nat.mul(al, b), Nat.mul(sa, b))
  +l2 = Nat.add(Nat.add(Nat.mul(al, bl), Nat.mul(al, sb)), Nat.mul(sa, b))
  +l3 = Nat.add(Nat.add(Nat.mul(al, bl), Nat.mul(al, sb)), Nat.add(Nat.mul(sa, bl), Nat.mul(sa, sb)))
  +l4 = Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(Nat.mul(sa, bl), Nat.mul(sa, sb)))
  +l5 = Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), Nat.mul(sa, sb)))
  Equal.trans(Nat, Nat.mul(Nat.add(al, sa), b), l1, Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))), NA.mul_add_right(al, sa, b),
    Equal.trans(Nat, l1, l2, Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))), cong_l(Nat.mul(al, b), Nat.add(Nat.mul(al, bl), Nat.mul(al, sb)), Nat.mul(sa, b), NA.mul_add_left(al, bl, sb)),
      Equal.trans(Nat, l2, l3, Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))), cong_r(Nat.add(Nat.mul(al, bl), Nat.mul(al, sb)), Nat.mul(sa, b), Nat.add(Nat.mul(sa, bl), Nat.mul(sa, sb)), NA.mul_add_left(sa, bl, sb)),
        Equal.trans(Nat, l3, l4, Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))), cong_l(Nat.add(Nat.mul(al, bl), Nat.mul(al, sb)), Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(Nat.mul(sa, bl), Nat.mul(sa, sb)), cong_r(Nat.mul(al, bl), Nat.mul(al, sb), WD.sc(16n, Nat.mul(al, bh)), mul_sc_r(16n, al, bh))),
          Equal.trans(Nat, l4, l5, Nat.add(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh)))), cong_r(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(Nat.mul(sa, bl), Nat.mul(sa, sb)), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), Nat.mul(sa, sb)), cong_l(Nat.mul(sa, bl), WD.sc(16n, Nat.mul(ah, bl)), Nat.mul(sa, sb), mul_sc_l(16n, ah, bl))),
            cong_r(Nat.add(Nat.mul(al, bl), WD.sc(16n, Nat.mul(al, bh))), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), Nat.mul(sa, sb)), Nat.add(WD.sc(16n, Nat.mul(ah, bl)), WD.sc(32n, Nat.mul(ah, bh))), cong_r(WD.sc(16n, Nat.mul(ah, bl)), Nat.mul(sa, sb), WD.sc(32n, Nat.mul(ah, bh)), e6)))))))

# 2^16 Mlo + (2^32 Mhi + 2^48 K) == 2^16 LH + 2^16 HL, from M == Mlo + 2^16 Mhi and M + 2^32 K == LH + HL
def mid_eq(+m: Nat, +k: Nat, +mlo: Nat, +mhi: Nat, +lh: Nat, +hl: Nat, +e3: {Nat.add(m, WD.sc(32n, k)) == Nat.add(lh, hl) : Nat}, +e5: {m == Nat.add(mlo, WD.sc(16n, mhi)) : Nat}) -> {Nat.add(WD.sc(16n, mlo), Nat.add(WD.sc(32n, mhi), WD.sc(48n, k))) == Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)) : Nat}:
  +a = WD.sc(16n, mlo)
  +b = WD.sc(32n, mhi)
  +c = WD.sc(48n, k)
  +x1 = Nat.add(Nat.add(a, b), c)
  +x2 = Nat.add(WD.sc(16n, m), c)
  +x3 = Nat.add(WD.sc(16n, m), WD.sc(16n, WD.sc(32n, k)))
  +x4 = WD.sc(16n, Nat.add(m, WD.sc(32n, k)))
  +x5 = WD.sc(16n, Nat.add(lh, hl))
  +eab = Equal.trans(Nat, Nat.add(a, b), Nat.add(a, WD.sc(16n, WD.sc(16n, mhi))), WD.sc(16n, m), cong_r(a, b, WD.sc(16n, WD.sc(16n, mhi)), Equal.sym(Nat, WD.sc(16n, WD.sc(16n, mhi)), b, sc_sc(16n, 16n, mhi))), Equal.trans(Nat, Nat.add(a, WD.sc(16n, WD.sc(16n, mhi))), WD.sc(16n, Nat.add(mlo, WD.sc(16n, mhi))), WD.sc(16n, m), A.sc_add(16n, mlo, WD.sc(16n, mhi)), cong_sc(16n, Nat.add(mlo, WD.sc(16n, mhi)), m, Equal.sym(Nat, m, Nat.add(mlo, WD.sc(16n, mhi)), e5))))
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), x1, Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), Equal.sym(Nat, x1, Nat.add(a, Nat.add(b, c)), NA.add_assoc(a, b, c)),
    Equal.trans(Nat, x1, x2, Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), cong_l(Nat.add(a, b), WD.sc(16n, m), c, eab),
      Equal.trans(Nat, x2, x3, Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), cong_r(WD.sc(16n, m), c, WD.sc(16n, WD.sc(32n, k)), Equal.sym(Nat, WD.sc(16n, WD.sc(32n, k)), c, sc_sc(16n, 32n, k))),
        Equal.trans(Nat, x3, x4, Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), A.sc_add(16n, m, WD.sc(32n, k)),
          Equal.trans(Nat, x4, x5, Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), cong_sc(16n, Nat.add(m, WD.sc(32n, k)), Nat.add(lh, hl), e3), sc_add2(16n, lh, hl))))))

# the value equation of the product: low word, carries and high digits
def assemble(+al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +m: Nat, +k: Nat, +mlo: Nat, +mhi: Nat, +vl: Nat, +c2: Nat, +e3: {Nat.add(m, WD.sc(32n, k)) == Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl)) : Nat}, +e5: {m == Nat.add(mlo, WD.sc(16n, mhi)) : Nat}, +e8: {Nat.add(vl, WD.sc(32n, c2)) == Nat.add(Nat.mul(al, bl), WD.sc(16n, mlo)) : Nat}) -> {Nat.add(vl, WD.sc(32n, Nat.add(Nat.add(Nat.mul(ah, bh), Nat.add(mhi, WD.sc(16n, k))), c2))) == Nat.mul(Nat.add(al, WD.sc(16n, ah)), Nat.add(bl, WD.sc(16n, bh))) : Nat}:
  +ll = Nat.mul(al, bl)
  +lh = Nat.mul(al, bh)
  +hl = Nat.mul(ah, bl)
  +hh = Nat.mul(ah, bh)
  +q = Nat.add(hh, Nat.add(mhi, WD.sc(16n, k)))
  +r = Nat.add(WD.sc(32n, mhi), WD.sc(48n, k))
  +sq = Nat.add(WD.sc(32n, hh), r)
  +eq = Equal.trans(Nat, WD.sc(32n, q), Nat.add(WD.sc(32n, hh), WD.sc(32n, Nat.add(mhi, WD.sc(16n, k)))), sq, sc_add2(32n, hh, Nat.add(mhi, WD.sc(16n, k))), cong_r(WD.sc(32n, hh), WD.sc(32n, Nat.add(mhi, WD.sc(16n, k))), r, Equal.trans(Nat, WD.sc(32n, Nat.add(mhi, WD.sc(16n, k))), Nat.add(WD.sc(32n, mhi), WD.sc(32n, WD.sc(16n, k))), r, sc_add2(32n, mhi, WD.sc(16n, k)), cong_r(WD.sc(32n, mhi), WD.sc(32n, WD.sc(16n, k)), WD.sc(48n, k), sc_sc(32n, 16n, k)))))
  +t1 = Nat.add(vl, Nat.add(WD.sc(32n, q), WD.sc(32n, c2)))
  +t2 = Nat.add(Nat.add(vl, WD.sc(32n, c2)), WD.sc(32n, q))
  +t3 = Nat.add(Nat.add(ll, WD.sc(16n, mlo)), sq)
  +t4 = Nat.add(Nat.add(ll, WD.sc(32n, hh)), Nat.add(WD.sc(16n, mlo), r))
  +t5 = Nat.add(Nat.add(ll, WD.sc(32n, hh)), Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)))
  +t6 = Nat.add(Nat.add(ll, WD.sc(16n, lh)), Nat.add(WD.sc(32n, hh), WD.sc(16n, hl)))
  +rr = Nat.add(Nat.add(ll, WD.sc(16n, lh)), Nat.add(WD.sc(16n, hl), WD.sc(32n, hh)))
  +swp = Equal.trans(Nat, Nat.add(vl, Nat.add(WD.sc(32n, q), WD.sc(32n, c2))), Nat.add(WD.sc(32n, q), Nat.add(vl, WD.sc(32n, c2))), t2, NA.add_swap(vl, WD.sc(32n, q), WD.sc(32n, c2)), NA.add_comm(WD.sc(32n, q), Nat.add(vl, WD.sc(32n, c2))))
  +chain = Equal.trans(Nat, Nat.add(vl, WD.sc(32n, Nat.add(q, c2))), t1, rr, cong_r(vl, WD.sc(32n, Nat.add(q, c2)), Nat.add(WD.sc(32n, q), WD.sc(32n, c2)), sc_add2(32n, q, c2)),
    Equal.trans(Nat, t1, t2, rr, swp,
      Equal.trans(Nat, t2, Nat.add(Nat.add(ll, WD.sc(16n, mlo)), WD.sc(32n, q)), rr, cong_l(Nat.add(vl, WD.sc(32n, c2)), Nat.add(ll, WD.sc(16n, mlo)), WD.sc(32n, q), e8),
        Equal.trans(Nat, Nat.add(Nat.add(ll, WD.sc(16n, mlo)), WD.sc(32n, q)), t3, rr, cong_r(Nat.add(ll, WD.sc(16n, mlo)), WD.sc(32n, q), sq, eq),
          Equal.trans(Nat, t3, t4, rr, add4(ll, WD.sc(16n, mlo), WD.sc(32n, hh), r),
            Equal.trans(Nat, t4, t5, rr, cong_r(Nat.add(ll, WD.sc(32n, hh)), Nat.add(WD.sc(16n, mlo), r), Nat.add(WD.sc(16n, lh), WD.sc(16n, hl)), mid_eq(m, k, mlo, mhi, lh, hl, e3, e5)),
              Equal.trans(Nat, t5, t6, rr, add4(ll, WD.sc(32n, hh), WD.sc(16n, lh), WD.sc(16n, hl)),
                cong_r(Nat.add(ll, WD.sc(16n, lh)), Nat.add(WD.sc(32n, hh), WD.sc(16n, hl)), Nat.add(WD.sc(16n, hl), WD.sc(32n, hh)), NA.add_comm(WD.sc(32n, hh), WD.sc(16n, hl))))))))))
  Equal.trans(Nat, Nat.add(vl, WD.sc(32n, Nat.add(q, c2))), rr, Nat.mul(Nat.add(al, WD.sc(16n, ah)), Nat.add(bl, WD.sc(16n, bh))), chain, Equal.sym(Nat, Nat.mul(Nat.add(al, WD.sc(16n, ah)), Nat.add(bl, WD.sc(16n, bh))), rr, expand16(al, ah, bl, bh)))

# ---- the U32 steps ----

def shift_sc(+k: Nat, +x: Nat) -> {C.shift(k, x) == WD.sc(k, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, x), WD.sc(p, x), shift_sc(p, x))

def mex(x: U32, y: U32) -> Nat:
  match x y:
    case U32{a} U32{b}:
      WM.excess(32n, 32n, a, b, Word.zero(32n))

# a wrapping product and its lost high part
def mul_cons(+x: U32, +y: U32) -> {Nat.add(v(U32.mul(x, y)), WD.sc(32n, mex(x, y))) == Nat.mul(v(x), v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      +p = Nat.mul(S.unsigned(32n, a), S.unsigned(32n, b))
      +lhs = Nat.add(S.unsigned(32n, Word.mul.go(32n, 32n, a, b, Word.zero(32n))), S.scale_binary(32n, WM.excess(32n, 32n, a, b, Word.zero(32n))))
      %Equal.sym(Nat, UD.v(U32{Word.mul(32n, a, b)}), WD.uw(32n, Word.mul(32n, a, b)), UD.vw(Word.mul(32n, a, b))) : {Nat.add(_, WD.sc(32n, WM.excess(32n, 32n, a, b, Word.zero(32n)))) == Nat.mul(UD.v(U32{a}), UD.v(U32{b})) : Nat}
      %Equal.sym(Nat, UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)) : {Nat.add(WD.uw(32n, Word.mul(32n, a, b)), WD.sc(32n, WM.excess(32n, 32n, a, b, Word.zero(32n)))) == Nat.mul(_, UD.v(U32{b})) : Nat}
      %Equal.sym(Nat, UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)) : {Nat.add(WD.uw(32n, Word.mul(32n, a, b)), WD.sc(32n, WM.excess(32n, 32n, a, b, Word.zero(32n)))) == Nat.mul(WD.uw(32n, a), _) : Nat}
      Equal.trans(Nat, lhs, Nat.add(S.unsigned(32n, Word.zero(32n)), p), p, WM.conservation(32n, 32n, a, b, Word.zero(32n)), cong_l(S.unsigned(32n, Word.zero(32n)), 0n, p, WM.zero_unsigned(32n)))

def b32_v(+c: Bool) -> {v(X.b32(c)) == S.bit_value(c) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def bit_le1(+c: Bool) -> {Nat.is_le(S.bit_value(c), 1n) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def one_lt_sc(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(1n, WD.sc(1n+k, one)) == True{} : Bool}:
  +p = L.subst(Nat, o => {Nat.is_lt(0n, WD.sc(k, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WD.sc_pos(k))
  N.lt_le_trans(1n, 1n+WD.sc(k, one), Nat.double(WD.sc(k, one)), N.lt_add_left(0n, WD.sc(k, one), 1n, p), N.double_succ_le(WD.sc(k, one), N.lt_succ_le_succ(0n, WD.sc(k, one), p)))

def bit_lt16(+one: Nat, +h1: {one == 1n : Nat}, +c: Bool) -> {Nat.is_lt(S.bit_value(c), WD.sc(16n, one)) == True{} : Bool}:
  N.le_lt_trans(S.bit_value(c), 1n, WD.sc(16n, one), bit_le1(c), one_lt_sc(15n, one, h1))

def prod_lt(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +y: Nat, +hx: {Nat.is_lt(x, WD.sc(16n, one)) == True{} : Bool}, +hy: {Nat.is_lt(y, WD.sc(16n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), WD.sc(32n, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.mul(x, y), z) == True{} : Bool}, Nat.mul(WD.sc(16n, one), WD.sc(16n, one)), WD.sc(32n, one), sq_sc(16n, one, h1), mul_lt_sq(x, y, WD.sc(16n, one), hx, hy))

# 2^16 x < 2^32 for x < 2^16
def sc16_lt(+one: Nat, +x: Nat, +hx: {Nat.is_lt(x, WD.sc(16n, one)) == True{} : Bool}) -> {Nat.is_lt(WD.sc(16n, x), WD.sc(32n, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(WD.sc(16n, x), z) == True{} : Bool}, WD.sc(16n, WD.sc(16n, one)), WD.sc(32n, one), sc_sc(16n, 16n, one), AR.sc_lt(16n, x, WD.sc(16n, one), hx))

# ---- the implementation with its 2^16 constants as parameters ----

def fin_g(+ll: U32, +mid: U32, +hh: U32, mc: Bool, +c: U32) -> WU.U64:
  X.add_fin(U32.add(ll, U32.mul(mid, c)), ll, hh, U32.add(U32.div(mid, c), U32.mul(X.b32(mc), c)))

def mid_g(+ll: U32, +lh: U32, +hl: U32, +hh: U32, +c: U32) -> WU.U64:
  fin_g(ll, U32.add(lh, hl), hh, U32.is_lt(U32.add(lh, hl), lh), c)

def h_g(+al: U32, +ah: U32, +bl: U32, +bh: U32, +c: U32) -> WU.U64:
  mid_g(U32.mul(al, bl), U32.mul(al, bh), U32.mul(ah, bl), U32.mul(ah, bh), c)

def mul32g(+a: U32, +b: U32, +c: U32, +m: U32) -> WU.U64:
  h_g(U32.and(a, m), U32.div(a, c), U32.and(b, m), U32.div(b, c), c)

def impl(+a: U32, +b: U32) -> {X.mul32(a, b) == mul32g(a, b, 65536, 65535) : WU.U64}:
  {==}

# the value of the generalised product, constants symbolic
def mulval(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +b: U32, +c: U32, +pc: {c == U32{WD.pw(32n, 16n)} : U32}, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}) -> {SW.value(mul32g(a, b, c, m)) == Nat.mul(v(a), v(b)) : Nat}:
  +al = U32.and(a, m)
  +ah = U32.div(a, c)
  +bl = U32.and(b, m)
  +bh = U32.div(b, c)
  +xal = v(al)
  +xah = v(ah)
  +xbl = v(bl)
  +xbh = v(bh)
  +bal = lo16_lt(one, h1, a, m, pm)
  +bah = hi16_lt(one, h1, a, c, pc)
  +bbl = lo16_lt(one, h1, b, m, pm)
  +bbh = hi16_lt(one, h1, b, c, pc)
  +ll = U32.mul(al, bl)
  +lh = U32.mul(al, bh)
  +hl = U32.mul(ah, bl)
  +hh = U32.mul(ah, bh)
  +pll = PD.mul32(one, h1, al, bl, prod_lt(one, h1, xal, xbl, bal, bbl))
  +plh = PD.mul32(one, h1, al, bh, prod_lt(one, h1, xal, xbh, bal, bbh))
  +phl = PD.mul32(one, h1, ah, bl, prod_lt(one, h1, xah, xbl, bah, bbl))
  +phh = PD.mul32(one, h1, ah, bh, prod_lt(one, h1, xah, xbh, bah, bbh))
  # the middle sum and its carry
  +mid = U32.add(lh, hl)
  +cm = P64.carry32(lh, hl)
  +kk = S.bit_value(cm)
  +mlo = lo16(mid, m)
  +mhi = hi16(mid, c)
  +e3a = P64.add_cons(lh, hl)
  +e3 = Equal.trans(Nat, Nat.add(v(mid), WD.sc(32n, kk)), Nat.add(v(lh), v(hl)), Nat.add(Nat.mul(xal, xbh), Nat.mul(xah, xbl)), e3a, Equal.trans(Nat, Nat.add(v(lh), v(hl)), Nat.add(Nat.mul(xal, xbh), v(hl)), Nat.add(Nat.mul(xal, xbh), Nat.mul(xah, xbl)), cong_l(v(lh), Nat.mul(xal, xbh), v(hl), plh), cong_r(Nat.mul(xal, xbh), v(hl), Nat.mul(xah, xbl), phl)))
  +e5 = split16(one, h1, mid, c, pc, m, pm)
  # the wrapped middle shift keeps the low half
  +mm = U32.mul(mid, c)
  +emc = mul_cons(mid, c)
  +e6a = Equal.trans(Nat, Nat.mul(v(mid), v(c)), WD.sc(16n, v(mid)), Nat.add(WD.sc(16n, mlo), WD.sc(32n, mhi)), PD.mul_pow(one, h1, 16n, v(mid), v(c), h16(one, h1, c, pc)), Equal.trans(Nat, WD.sc(16n, v(mid)), WD.sc(16n, Nat.add(mlo, WD.sc(16n, mhi))), Nat.add(WD.sc(16n, mlo), WD.sc(32n, mhi)), cong_sc(16n, v(mid), Nat.add(mlo, WD.sc(16n, mhi)), e5), Equal.trans(Nat, WD.sc(16n, Nat.add(mlo, WD.sc(16n, mhi))), Nat.add(WD.sc(16n, mlo), WD.sc(16n, WD.sc(16n, mhi))), Nat.add(WD.sc(16n, mlo), WD.sc(32n, mhi)), sc_add2(16n, mlo, WD.sc(16n, mhi)), cong_r(WD.sc(16n, mlo), WD.sc(16n, WD.sc(16n, mhi)), WD.sc(32n, mhi), sc_sc(16n, 16n, mhi)))))
  +e6 = Equal.trans(Nat, Nat.add(v(mm), WD.sc(32n, mex(mid, c))), Nat.mul(v(mid), v(c)), Nat.add(WD.sc(16n, mlo), WD.sc(32n, mhi)), emc, e6a)
  +e7 = WD.uniq(32n, one, h1, v(mm), WD.sc(16n, mlo), mex(mid, c), mhi, e6, UD.vb(one, h1, mm), sc16_lt(one, mlo, lo16_lt(one, h1, mid, m, pm)))
  # the low word
  +lo = U32.add(ll, mm)
  +c2 = P64.carry32(ll, mm)
  +e8a = P64.add_cons(ll, mm)
  +e8 = Equal.trans(Nat, Nat.add(v(lo), WD.sc(32n, S.bit_value(c2))), Nat.add(v(ll), v(mm)), Nat.add(Nat.mul(xal, xbl), WD.sc(16n, mlo)), e8a, Equal.trans(Nat, Nat.add(v(ll), v(mm)), Nat.add(Nat.mul(xal, xbl), v(mm)), Nat.add(Nat.mul(xal, xbl), WD.sc(16n, mlo)), cong_l(v(ll), Nat.mul(xal, xbl), v(mm), pll), cong_r(Nat.mul(xal, xbl), v(mm), WD.sc(16n, mlo), e7)))
  # the total, as numbers
  +q = Nat.add(Nat.add(Nat.mul(xah, xbh), Nat.add(mhi, WD.sc(16n, kk))), S.bit_value(c2))
  +tot = assemble(xal, xah, xbl, xbh, v(mid), kk, mlo, mhi, v(lo), S.bit_value(c2), e3, e5, e8)
  +ea = split16(one, h1, a, c, pc, m, pm)
  +eb = split16(one, h1, b, c, pc, m, pm)
  +eab = Equal.trans(Nat, Nat.mul(Nat.add(xal, WD.sc(16n, xah)), Nat.add(xbl, WD.sc(16n, xbh))), Nat.mul(v(a), Nat.add(xbl, WD.sc(16n, xbh))), Nat.mul(v(a), v(b)), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.add(xbl, WD.sc(16n, xbh))), Nat.add(xal, WD.sc(16n, xah)), v(a), Equal.sym(Nat, v(a), Nat.add(xal, WD.sc(16n, xah)), ea)), Equal.cong(Nat, Nat, t => Nat.mul(v(a), t), Nat.add(xbl, WD.sc(16n, xbh)), v(b), Equal.sym(Nat, v(b), Nat.add(xbl, WD.sc(16n, xbh)), eb)))
  +etot = Equal.trans(Nat, Nat.add(v(lo), WD.sc(32n, q)), Nat.mul(Nat.add(xal, WD.sc(16n, xah)), Nat.add(xbl, WD.sc(16n, xbh))), Nat.mul(v(a), v(b)), tot, eab)
  # the high word does not wrap: 2^32 q <= a b < 2^64
  +pab = L.subst(Nat, z => {Nat.is_lt(Nat.mul(v(a), v(b)), z) == True{} : Bool}, Nat.mul(WD.sc(32n, one), WD.sc(32n, one)), WD.sc(64n, one), sq_sc(32n, one, h1), mul_lt_sq(v(a), v(b), WD.sc(32n, one), UD.vb(one, h1, a), UD.vb(one, h1, b)))
  +lq = L.subst(Nat, z => {Nat.is_le(WD.sc(32n, q), z) == True{} : Bool}, Nat.add(WD.sc(32n, q), v(lo)), Nat.mul(v(a), v(b)), Equal.trans(Nat, Nat.add(WD.sc(32n, q), v(lo)), Nat.add(v(lo), WD.sc(32n, q)), Nat.mul(v(a), v(b)), NA.add_comm(WD.sc(32n, q), v(lo)), etot), N.le_add_right(WD.sc(32n, q), v(lo)))
  +bq = AR.sc_lt_cancel(32n, q, WD.sc(32n, one), L.subst(Nat, z => {Nat.is_lt(WD.sc(32n, q), z) == True{} : Bool}, WD.sc(64n, one), WD.sc(32n, WD.sc(32n, one)), AR.sc_idx(32n, 32n, one), N.le_lt_trans(WD.sc(32n, q), Nat.mul(v(a), v(b)), WD.sc(64n, one), lq, pab)))
  # the high word's value is q
  +mc = U32.is_lt(mid, lh)
  +emc2 = P64.add_lt(lh, hl)
  +tb = U32.mul(X.b32(mc), c)
  +vb32 = Equal.trans(Nat, v(X.b32(mc)), S.bit_value(mc), kk, b32_v(mc), Equal.cong(Bool, Nat, t => S.bit_value(t), mc, cm, emc2))
  +btb = L.subst(Nat, z => {Nat.is_lt(WD.sc(16n, z), WD.sc(32n, one)) == True{} : Bool}, S.bit_value(mc), v(X.b32(mc)), Equal.sym(Nat, v(X.b32(mc)), S.bit_value(mc), b32_v(mc)), sc16_lt(one, S.bit_value(mc), bit_lt16(one, h1, mc)))
  +ptb = Equal.trans(Nat, v(tb), WD.sc(16n, v(X.b32(mc))), WD.sc(16n, kk), PD.mulp32(one, h1, 16n, X.b32(mc), c, h16(one, h1, c, pc), btb), cong_sc(16n, v(X.b32(mc)), kk, vb32))
  +bt = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.add(WD.sc(16n, kk), mhi), Nat.add(mhi, WD.sc(16n, kk)), NA.add_comm(WD.sc(16n, kk), mhi), L.subst(Nat, z => {Nat.is_lt(Nat.add(WD.sc(16n, kk), mhi), z) == True{} : Bool}, WD.sc(16n, WD.sc(16n, one)), WD.sc(32n, one), sc_sc(16n, 16n, one), AR.digit_lt(16n, one, h1, mhi, kk, WD.sc(16n, one), hi16_lt(one, h1, mid, c, pc), bit_lt16(one, h1, cm))))
  +t = U32.add(U32.div(mid, c), tb)
  +pt = PD.addv32(one, h1, U32.div(mid, c), tb, mhi, WD.sc(16n, kk), {==}, ptb, bt)
  +q1 = Nat.add(Nat.mul(xah, xbh), Nat.add(mhi, WD.sc(16n, kk)))
  +bq1 = N.le_lt_trans(q1, q, WD.sc(32n, one), N.le_add_right(q1, S.bit_value(c2)), bq)
  +h1v = PD.addv32(one, h1, hh, t, Nat.mul(xah, xbh), Nat.add(mhi, WD.sc(16n, kk)), phh, pt, bq1)
  +ec2 = Equal.trans(Nat, v(X.b32(U32.is_lt(lo, ll))), S.bit_value(U32.is_lt(lo, ll)), S.bit_value(c2), b32_v(U32.is_lt(lo, ll)), Equal.cong(Bool, Nat, t2 => S.bit_value(t2), U32.is_lt(lo, ll), c2, P64.add_lt(ll, mm)))
  +hv = PD.addv32(one, h1, U32.add(hh, t), X.b32(U32.is_lt(lo, ll)), q1, S.bit_value(c2), h1v, ec2, bq)
  # the value of the pair
  +hi = U32.add(U32.add(hh, t), X.b32(U32.is_lt(lo, ll)))
  +ev = Equal.trans(Nat, Nat.add(v(lo), C.shift(32n, v(hi))), Nat.add(v(lo), WD.sc(32n, v(hi))), Nat.add(v(lo), WD.sc(32n, q)), cong_r(v(lo), C.shift(32n, v(hi)), WD.sc(32n, v(hi)), shift_sc(32n, v(hi))), cong_r(v(lo), WD.sc(32n, v(hi)), WD.sc(32n, q), cong_sc(32n, v(hi), q, hv)))
  Equal.trans(Nat, Nat.add(v(lo), C.shift(32n, v(hi))), Nat.add(v(lo), WD.sc(32n, q)), Nat.mul(v(a), v(b)), ev, etot)

# Mul32.value: the full product of two U32
def mul32_value(+a: U32, +b: U32) -> SW.Mul32.value(a, b):
  %Equal.sym(WU.U64, X.mul32(a, b), mul32g(a, b, 65536, 65535), impl(a, b)) : {SW.value(_) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}
  mulval(1n, {==}, a, b, 65536, {==}, 65535, {==})
