import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/lemmas/spec/numeric.bend as S
import ../natural/arith.bend as NR
import ../u64/u64div.bend as PD
import ./w64mul.bend as W64M
import ./w64add.bend as WA
import ./width.bend as WW
import ./u32laws.bend as LW

# Shifts and leading zeros of src/math/w64.bend (the software F64's
# significand arithmetic) against spec/math/w64.bend: a shift right is
# high(k, a) (Mathlib Nat.shiftRight_eq_div_pow), a shift left low(64, a 2^k)
# (Nat.shiftLeft_eq), each limb's piece recombined through the uniqueness of
# n == low(k, n) + 2^k high(k, n).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def vb(+x: U32) -> {C.fits(32n, v(x)) == True{} : Bool}:
  LW.vb(x)

# the 2^k table is the word with bit k set
def p2w(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {X.pow2(k) == U32{WD.pw(32n, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n+j:
      Empty.absurd({X.pow2(32n+j) == U32{WD.pw(32n, 32n+j)} : U32}, N.lt_zero_absurd(j, hk))

def p2v(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {v(X.pow2(k)) == C.pow2(k) : Nat}:
  Equal.trans(Nat, v(X.pow2(k)), WD.sc(k, 1n), C.pow2(k), PD.pow32(k, hk, 1n, {==}, X.pow2(k), p2w(k, hk)), Equal.sym(Nat, C.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)))

def pow2_eq(+k: Nat) -> {C.pow2(k) == 1n+Nat.sub(C.pow2(k), 1n) : Nat}:
  Equal.sym(Nat, 1n+Nat.sub(C.pow2(k), 1n), C.pow2(k), N.sub_add(C.pow2(k), 1n, N.pow2_pos(k)))

# x / 2^k on a word is high(k, x)
def div_p2(+x: U32, +k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {v(U32.div(x, X.pow2(k))) == C.high(k, v(x)) : Nat}:
  +pp = Nat.sub(C.pow2(k), 1n)
  +ev = Equal.trans(Nat, v(X.pow2(k)), C.pow2(k), 1n+pp, p2v(k, hk), pow2_eq(k))
  +nz = LW.nz(X.pow2(k), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(X.pow2(k)), 1n+pp, ev))
  Equal.trans(Nat, v(U32.div(x, X.pow2(k))), Nat.div(v(x), v(X.pow2(k))), C.high(k, v(x)), UD.div_nat(x, X.pow2(k), nz), Equal.trans(Nat, Nat.div(v(x), v(X.pow2(k))), Nat.div(v(x), 1n+pp), C.high(k, v(x)), Equal.cong(Nat, Nat, t => Nat.div(v(x), t), v(X.pow2(k)), 1n+pp, ev), Equal.sym(Nat, C.high(k, v(x)), Nat.div(v(x), 1n+pp), WW.high_div(k, v(x), pp, pow2_eq(k)))))

# a word product wraps mod 2^32
def mul_low(+x: U32, +y: U32) -> {v(U32.mul(x, y)) == C.low(32n, Nat.mul(v(x), v(y))) : Nat}:
  +e = WA.mcons(x, y)
  Equal.sym(Nat, C.low(32n, Nat.mul(v(x), v(y))), v(U32.mul(x, y)), Equal.trans(Nat, C.low(32n, Nat.mul(v(x), v(y))), C.low(32n, Nat.add(v(U32.mul(x, y)), C.shift(32n, W64M.mex(x, y)))), v(U32.mul(x, y)), Equal.cong(Nat, Nat, t => C.low(32n, t), Nat.mul(v(x), v(y)), Nat.add(v(U32.mul(x, y)), C.shift(32n, W64M.mex(x, y))), Equal.sym(Nat, Nat.add(v(U32.mul(x, y)), C.shift(32n, W64M.mex(x, y))), Nat.mul(v(x), v(y)), e)), WW.low_u(32n, v(U32.mul(x, y)), W64M.mex(x, y), vb(U32.mul(x, y)))))

# x 2^k on a word: low(32, shift(k, x))
def mul_p2(+x: U32, +k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {v(U32.mul(x, X.pow2(k))) == C.low(32n, C.shift(k, v(x))) : Nat}:
  +e = Equal.trans(Nat, Nat.mul(v(x), v(X.pow2(k))), Nat.mul(v(x), C.shift(k, 1n)), C.shift(k, v(x)), Equal.cong(Nat, Nat, t => Nat.mul(v(x), t), v(X.pow2(k)), C.shift(k, 1n), Equal.trans(Nat, v(X.pow2(k)), C.pow2(k), C.shift(k, 1n), p2v(k, hk), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), WW.shift_one(k)))), Equal.sym(Nat, C.shift(k, v(x)), Nat.mul(v(x), C.shift(k, 1n)), WW.shift_mul(k, v(x))))
  Equal.trans(Nat, v(U32.mul(x, X.pow2(k))), C.low(32n, Nat.mul(v(x), v(X.pow2(k)))), C.low(32n, C.shift(k, v(x))), mul_low(x, X.pow2(k)), Equal.cong(Nat, Nat, t => C.low(32n, t), Nat.mul(v(x), v(X.pow2(k))), C.shift(k, v(x)), e))

def fits_high(+t: Nat, +s: Nat, +x: Nat, +h: {C.fits(Nat.add(t, s), x) == True{} : Bool}) -> {C.fits(s, C.high(t, x)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(z, 0n) == True{} : Bool}, C.high(Nat.add(t, s), x), C.high(s, C.high(t, x)), WW.high_comp(s, t, x), h)

def fits_mono(+a: Nat, +b: Nat, +x: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +h: {C.fits(a, x) == True{} : Bool}) -> {C.fits(b, x) == True{} : Bool}:
  WW.fits_of_lt(b, x, N.lt_le_trans(x, C.pow2(a), C.pow2(b), WW.lt_of_fits(a, x, h), N.pow2_mono(a, b, hab)))

def val(+l: U32, +h: U32) -> Nat:
  Nat.add(v(l), C.shift(32n, v(h)))

def fit64(+l: U32, +h: U32) -> {C.fits(64n, val(l, h)) == True{} : Bool}:
  WW.limbs_fit(32n, 32n, v(l), v(h), vb(l), vb(h))

def val0(+x: U32) -> {SW.value(WU.U64{x, 0}) == v(x) : Nat}:
  Equal.trans(Nat, Nat.add(v(x), C.shift(32n, 0n)), Nat.add(v(x), 0n), v(x), Equal.cong(Nat, Nat, z => Nat.add(v(x), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(x)))

def fits32(+t: Nat, +s: Nat, +hts: {Nat.add(t, s) == 32n : Nat}, +x: U32) -> {C.fits(Nat.add(t, s), v(x)) == True{} : Bool}:
  L.subst(Nat, z => {C.fits(z, v(x)) == True{} : Bool}, 32n, Nat.add(t, s), Equal.sym(Nat, Nat.add(t, s), 32n, hts), vb(x))

# 1 <= t < 32, s == 32 - t
def shr_small(+l: U32, +h: U32, +j: Nat, +hk: {Nat.is_lt(1n+j, 32n) == True{} : Bool}) -> {SW.value(X.shr_lt(WU.U64{l, h}, 1n+j)) == C.high(1n+j, val(l, h)) : Nat}:
  +t = {1n+j : Nat}
  +s = Nat.sub(32n, t)
  +hts = N.sub_add(32n, t, N.lt_le(t, 32n, hk))
  +hst = Equal.trans(Nat, Nat.add(s, t), Nat.add(t, s), 32n, N.add_comm(s, t), hts)
  +hs = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, Nat.add(t, s), 32n, hts, N.le_lt_trans(s, Nat.add(j, s), 1n+Nat.add(j, s), L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, Nat.add(s, j), Nat.add(j, s), N.add_comm(s, j), N.le_add_right(s, j)), N.lt_succ(Nat.add(j, s))))
  +hl = C.high(t, v(l))
  +lh = C.low(t, v(h))
  +hh = C.high(t, v(h))
  +a1 = div_p2(l, t, hk)
  +a2 = Equal.trans(Nat, v(U32.mul(h, X.pow2(s))), C.low(32n, C.shift(s, v(h))), C.shift(s, lh), mul_p2(h, s, hs), Equal.trans(Nat, C.low(32n, C.shift(s, v(h))), C.low(Nat.add(s, t), C.shift(s, v(h))), C.shift(s, lh), Equal.cong(Nat, Nat, z => C.low(z, C.shift(s, v(h))), 32n, Nat.add(s, t), Equal.sym(Nat, Nat.add(s, t), 32n, hst)), WW.low_shift(s, t, v(h))))
  +a3 = div_p2(h, t, hk)
  +hr = WW.lt_of_fits(s, hl, fits_high(t, s, v(l), fits32(t, s, hts, l)))
  +hsum = WW.two_limb_lt(s, t, hl, lh, hr, WW.low_lt(t, v(h)))
  +es = Equal.trans(Nat, Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s)))), Nat.add(hl, v(U32.mul(h, X.pow2(s)))), Nat.add(hl, C.shift(s, lh)), Equal.cong(Nat, Nat, z => Nat.add(z, v(U32.mul(h, X.pow2(s)))), v(U32.div(l, X.pow2(t))), hl, a1), Equal.cong(Nat, Nat, z => Nat.add(hl, z), v(U32.mul(h, X.pow2(s))), C.shift(s, lh), a2))
  +hf = L.subst(Nat, z => {C.fits(z, Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s))))) == True{} : Bool}, Nat.add(s, t), 32n, hst, WW.fits_of_lt(Nat.add(s, t), Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s)))), L.subst(Nat, z => {Nat.is_lt(z, C.pow2(Nat.add(s, t))) == True{} : Bool}, Nat.add(hl, C.shift(s, lh)), Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s)))), Equal.sym(Nat, Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s)))), Nat.add(hl, C.shift(s, lh)), es), hsum)))
  +elo = Equal.trans(Nat, v(U32.add(U32.div(l, X.pow2(t)), U32.mul(h, X.pow2(s)))), Nat.add(v(U32.div(l, X.pow2(t))), v(U32.mul(h, X.pow2(s)))), Nat.add(hl, C.shift(s, lh)), WA.add_exact(1n, {==}, U32.div(l, X.pow2(t)), U32.mul(h, X.pow2(s)), hf), es)
  +ev = Equal.trans(Nat, Nat.add(v(U32.add(U32.div(l, X.pow2(t)), U32.mul(h, X.pow2(s)))), C.shift(32n, v(U32.div(h, X.pow2(t))))), Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, v(U32.div(h, X.pow2(t))))), Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, hh)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(U32.div(h, X.pow2(t))))), v(U32.add(U32.div(l, X.pow2(t)), U32.mul(h, X.pow2(s)))), Nat.add(hl, C.shift(s, lh)), elo), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, z)), v(U32.div(h, X.pow2(t))), hh, a3))
  +e32 = Equal.trans(Nat, C.shift(32n, v(h)), C.shift(Nat.add(t, s), v(h)), C.shift(t, C.shift(s, v(h))), Equal.cong(Nat, Nat, z => C.shift(z, v(h)), 32n, Nat.add(t, s), Equal.sym(Nat, Nat.add(t, s), 32n, hts)), WW.shift_comp(t, s, v(h)))
  +eh1 = Equal.trans(Nat, C.high(t, val(l, h)), C.high(t, Nat.add(v(l), C.shift(t, C.shift(s, v(h))))), Nat.add(hl, C.shift(s, v(h))), Equal.cong(Nat, Nat, z => C.high(t, Nat.add(v(l), z)), C.shift(32n, v(h)), C.shift(t, C.shift(s, v(h))), e32), WW.high_add_shift(t, v(l), C.shift(s, v(h))))
  +esh = Equal.trans(Nat, C.shift(s, v(h)), C.shift(s, Nat.add(lh, C.shift(t, hh))), Nat.add(C.shift(s, lh), C.shift(32n, hh)), Equal.cong(Nat, Nat, z => C.shift(s, z), v(h), Nat.add(lh, C.shift(t, hh)), WW.low_high(t, v(h))), Equal.trans(Nat, C.shift(s, Nat.add(lh, C.shift(t, hh))), Nat.add(C.shift(s, lh), C.shift(s, C.shift(t, hh))), Nat.add(C.shift(s, lh), C.shift(32n, hh)), WW.shift_add(s, lh, C.shift(t, hh)), Equal.cong(Nat, Nat, z => Nat.add(C.shift(s, lh), z), C.shift(s, C.shift(t, hh)), C.shift(32n, hh), Equal.trans(Nat, C.shift(s, C.shift(t, hh)), C.shift(Nat.add(s, t), hh), C.shift(32n, hh), Equal.sym(Nat, C.shift(Nat.add(s, t), hh), C.shift(s, C.shift(t, hh)), WW.shift_comp(s, t, hh)), Equal.cong(Nat, Nat, z => C.shift(z, hh), Nat.add(s, t), 32n, hst)))))
  +et = Equal.trans(Nat, C.high(t, val(l, h)), Nat.add(hl, Nat.add(C.shift(s, lh), C.shift(32n, hh))), Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, hh)), Equal.trans(Nat, C.high(t, val(l, h)), Nat.add(hl, C.shift(s, v(h))), Nat.add(hl, Nat.add(C.shift(s, lh), C.shift(32n, hh))), eh1, Equal.cong(Nat, Nat, z => Nat.add(hl, z), C.shift(s, v(h)), Nat.add(C.shift(s, lh), C.shift(32n, hh)), esh)), Equal.sym(Nat, Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, hh)), Nat.add(hl, Nat.add(C.shift(s, lh), C.shift(32n, hh))), NA.add_assoc(hl, C.shift(s, lh), C.shift(32n, hh))))
  Equal.trans(Nat, Nat.add(v(U32.add(U32.div(l, X.pow2(t)), U32.mul(h, X.pow2(s)))), C.shift(32n, v(U32.div(h, X.pow2(t))))), Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, hh)), C.high(t, val(l, h)), ev, Equal.sym(Nat, C.high(t, val(l, h)), Nat.add(Nat.add(hl, C.shift(s, lh)), C.shift(32n, hh)), et))

def zero64(+l: U32, +h: U32, +k: Nat, +hk: {Nat.is_le(64n, k) == True{} : Bool}) -> {SW.value(WU.U64{0, 0}) == C.high(k, val(l, h)) : Nat}:
  +hf = fits_mono(64n, k, val(l, h), hk, fit64(l, h))
  Equal.trans(Nat, SW.value(WU.U64{0, 0}), v(0), C.high(k, val(l, h)), val0(0), Equal.sym(Nat, C.high(k, val(l, h)), 0n, N.eq_from_is_eq(C.high(k, val(l, h)), 0n, hf)))

# 32 <= k < 64: the high word shifted by k - 32
def shr_big(+l: U32, +h: U32, +k: Nat, +hge: {Nat.is_le(32n, k) == True{} : Bool}, +hlt: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {SW.value(WU.U64{U32.div(h, X.pow2(Nat.sub(k, 32n))), 0}) == C.high(k, val(l, h)) : Nat}:
  +d = Nat.sub(k, 32n)
  +ek = N.sub_add(k, 32n, hge)
  +hd = L.subst(Nat, z => {Nat.is_lt(d, z) == True{} : Bool}, Nat.sub(64n, 32n), 32n, {==}, WW.sub_lt_sub(k, 64n, 32n, hlt, hge))
  +e1 = Equal.trans(Nat, C.high(k, val(l, h)), C.high(Nat.add(32n, d), val(l, h)), C.high(d, C.high(32n, val(l, h))), Equal.cong(Nat, Nat, z => C.high(z, val(l, h)), k, Nat.add(32n, d), Equal.sym(Nat, Nat.add(32n, d), k, ek)), WW.high_comp(d, 32n, val(l, h)))
  +e2 = Equal.trans(Nat, C.high(k, val(l, h)), C.high(d, C.high(32n, val(l, h))), C.high(d, v(h)), e1, Equal.cong(Nat, Nat, z => C.high(d, z), C.high(32n, val(l, h)), v(h), WW.high_u(32n, v(l), v(h), vb(l))))
  Equal.trans(Nat, SW.value(WU.U64{U32.div(h, X.pow2(d)), 0}), v(U32.div(h, X.pow2(d))), C.high(k, val(l, h)), val0(U32.div(h, X.pow2(d))), Equal.trans(Nat, v(U32.div(h, X.pow2(d))), C.high(d, v(h)), C.high(k, val(l, h)), div_p2(h, d, hd), Equal.sym(Nat, C.high(k, val(l, h)), C.high(d, v(h)), e2)))

def shr_ge_c(+l: U32, +h: U32, +k: Nat, +hge: {Nat.is_le(32n, k) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(64n, k) == c : Bool}) -> {SW.value(X.shr_ge(WU.U64{l, h}, k, c)) == C.high(k, val(l, h)) : Nat}:
  match c:
    case True{}:
      zero64(l, h, k, hc)
    case False{}:
      shr_big(l, h, k, hge, N.not_le_lt(64n, k, hc))

def shr_c(+l: U32, +h: U32, +k: Nat, +c: Bool, +hc: {Nat.is_lt(k, 32n) == c : Bool}) -> {SW.value(X.shr_pick(WU.U64{l, h}, k, c)) == C.high(k, val(l, h)) : Nat}:
  match k c:
    case 0n True{}:
      {==}
    case 1n+ +j True{}:
      shr_small(l, h, j, hc)
    case _ False{}:
      shr_ge_c(l, h, k, N.not_lt_le(k, 32n, hc), Nat.is_le(64n, k), {==})

def shr_value(+a: WU.U64, +k: Nat) -> SW.Shr.value(a, k):
  match a:
    case WU.U64{+l, +h}:
      shr_c(l, h, k, Nat.is_lt(k, 32n), {==})

def shift_swap(+a: Nat, +b: Nat, +x: Nat) -> {C.shift(a, C.shift(b, x)) == C.shift(b, C.shift(a, x)) : Nat}:
  Equal.trans(Nat, C.shift(a, C.shift(b, x)), C.shift(Nat.add(a, b), x), C.shift(b, C.shift(a, x)), Equal.sym(Nat, C.shift(Nat.add(a, b), x), C.shift(a, C.shift(b, x)), WW.shift_comp(a, b, x)), Equal.trans(Nat, C.shift(Nat.add(a, b), x), C.shift(Nat.add(b, a), x), C.shift(b, C.shift(a, x)), Equal.cong(Nat, Nat, z => C.shift(z, x), Nat.add(a, b), Nat.add(b, a), N.add_comm(a, b)), WW.shift_comp(b, a, x)))

# shift(t, a) in 32-bit pieces, t + s == 32
def shl_eq(+t: Nat, +s: Nat, +hts: {Nat.add(t, s) == 32n : Nat}, +l: U32, +h: U32) -> {C.shift(t, Nat.add(v(l), C.shift(32n, v(h)))) == Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))) : Nat}:
  Equal.trans(Nat, C.shift(t, Nat.add(v(l), C.shift(32n, v(h)))), Nat.add(C.shift(t, v(l)), C.shift(t, C.shift(32n, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), WW.shift_add(t, v(l), C.shift(32n, v(h))), Equal.trans(Nat, Nat.add(C.shift(t, v(l)), C.shift(t, C.shift(32n, v(h)))), Nat.add(C.shift(t, v(l)), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, v(l)), z), C.shift(t, C.shift(32n, v(h))), C.shift(32n, C.shift(t, v(h))), shift_swap(t, 32n, v(h))), Equal.trans(Nat, Nat.add(C.shift(t, v(l)), C.shift(32n, C.shift(t, v(h)))), Nat.add(C.shift(t, Nat.add(C.low(s, v(l)), C.shift(s, C.high(s, v(l))))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, z), C.shift(32n, C.shift(t, v(h)))), v(l), Nat.add(C.low(s, v(l)), C.shift(s, C.high(s, v(l)))), WW.low_high(s, v(l))), Equal.trans(Nat, Nat.add(C.shift(t, Nat.add(C.low(s, v(l)), C.shift(s, C.high(s, v(l))))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(t, C.shift(s, C.high(s, v(l))))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.shift(t, v(h)))), C.shift(t, Nat.add(C.low(s, v(l)), C.shift(s, C.high(s, v(l))))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(t, C.shift(s, C.high(s, v(l))))), WW.shift_add(t, C.low(s, v(l)), C.shift(s, C.high(s, v(l))))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(t, C.shift(s, C.high(s, v(l))))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), z), C.shift(32n, C.shift(t, v(h)))), C.shift(t, C.shift(s, C.high(s, v(l)))), C.shift(32n, C.high(s, v(l))), Equal.trans(Nat, C.shift(t, C.shift(s, C.high(s, v(l)))), C.shift(Nat.add(t, s), C.high(s, v(l))), C.shift(32n, C.high(s, v(l))), Equal.sym(Nat, C.shift(Nat.add(t, s), C.high(s, v(l))), C.shift(t, C.shift(s, C.high(s, v(l)))), WW.shift_comp(t, s, C.high(s, v(l)))), Equal.cong(Nat, Nat, z => C.shift(z, C.high(s, v(l))), Nat.add(t, s), 32n, hts))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, C.shift(t, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, C.shift(t, Nat.add(C.low(s, v(h)), C.shift(s, C.high(s, v(h))))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, C.shift(t, z))), v(h), Nat.add(C.low(s, v(h)), C.shift(s, C.high(s, v(h)))), WW.low_high(s, v(h))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, C.shift(t, Nat.add(C.low(s, v(h)), C.shift(s, C.high(s, v(h))))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), C.shift(t, C.shift(s, C.high(s, v(h))))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, z)), C.shift(t, Nat.add(C.low(s, v(h)), C.shift(s, C.high(s, v(h))))), Nat.add(C.shift(t, C.low(s, v(h))), C.shift(t, C.shift(s, C.high(s, v(h))))), WW.shift_add(t, C.low(s, v(h)), C.shift(s, C.high(s, v(h))))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), C.shift(t, C.shift(s, C.high(s, v(h))))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), z))), C.shift(t, C.shift(s, C.high(s, v(h)))), C.shift(32n, C.high(s, v(h))), Equal.trans(Nat, C.shift(t, C.shift(s, C.high(s, v(h)))), C.shift(Nat.add(t, s), C.high(s, v(h))), C.shift(32n, C.high(s, v(h))), Equal.sym(Nat, C.shift(Nat.add(t, s), C.high(s, v(h))), C.shift(t, C.shift(s, C.high(s, v(h)))), WW.shift_comp(t, s, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => C.shift(z, C.high(s, v(h))), Nat.add(t, s), 32n, hts))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), z), C.shift(32n, Nat.add(C.shift(t, C.low(s, v(h))), C.shift(32n, C.high(s, v(h))))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h))))), WW.shift_add(32n, C.shift(t, C.low(s, v(h))), C.shift(32n, C.high(s, v(h))))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l)))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(C.shift(32n, C.high(s, v(l))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h))))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), NA.add_assoc(C.shift(t, C.low(s, v(l))), C.shift(32n, C.high(s, v(l))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Equal.trans(Nat, Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(C.shift(32n, C.high(s, v(l))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h))))))), Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, C.low(s, v(l))), z), Nat.add(C.shift(32n, C.high(s, v(l))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h))))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h))))), Nat.add(C.shift(32n, C.high(s, v(l))), Nat.add(C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), NA.add_assoc(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h)))), C.shift(32n, C.shift(32n, C.high(s, v(h))))))), Equal.trans(Nat, Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(z, C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), Equal.sym(Nat, C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), Nat.add(C.shift(32n, C.high(s, v(l))), C.shift(32n, C.shift(t, C.low(s, v(h))))), WW.shift_add(32n, C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), Equal.trans(Nat, Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(32n, C.shift(32n, C.high(s, v(h))))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(32n, C.shift(32n, C.high(s, v(h))))), Nat.add(C.shift(t, C.low(s, v(l))), Nat.add(C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), NA.add_assoc(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))), C.shift(32n, C.shift(32n, C.high(s, v(h)))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), z), C.shift(32n, C.shift(32n, C.high(s, v(h)))), C.shift(64n, C.high(s, v(h))), Equal.sym(Nat, C.shift(64n, C.high(s, v(h))), C.shift(32n, C.shift(32n, C.high(s, v(h)))), WW.shift_comp(32n, 32n, C.high(s, v(h))))))))))))))))))

def shl_small(+l: U32, +h: U32, +j: Nat, +hk: {Nat.is_lt(1n+j, 32n) == True{} : Bool}) -> {SW.value(X.shl_lt(WU.U64{l, h}, 1n+j)) == C.low(64n, C.shift(1n+j, val(l, h))) : Nat}:
  +t = {1n+j : Nat}
  +s = Nat.sub(32n, t)
  +hts = N.sub_add(32n, t, N.lt_le(t, 32n, hk))
  +hst = Equal.trans(Nat, Nat.add(s, t), Nat.add(t, s), 32n, N.add_comm(s, t), hts)
  +hs = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, Nat.add(t, s), 32n, hts, N.le_lt_trans(s, Nat.add(j, s), 1n+Nat.add(j, s), L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, Nat.add(s, j), Nat.add(j, s), N.add_comm(s, j), N.le_add_right(s, j)), N.lt_succ(Nat.add(j, s))))
  +a1 = Equal.trans(Nat, v(U32.mul(l, X.pow2(t))), C.low(32n, C.shift(t, v(l))), C.shift(t, C.low(s, v(l))), mul_p2(l, t, hk), Equal.trans(Nat, C.low(32n, C.shift(t, v(l))), C.low(Nat.add(t, s), C.shift(t, v(l))), C.shift(t, C.low(s, v(l))), Equal.cong(Nat, Nat, z => C.low(z, C.shift(t, v(l))), 32n, Nat.add(t, s), Equal.sym(Nat, Nat.add(t, s), 32n, hts)), WW.low_shift(t, s, v(l))))
  +a2 = Equal.trans(Nat, v(U32.mul(h, X.pow2(t))), C.low(32n, C.shift(t, v(h))), C.shift(t, C.low(s, v(h))), mul_p2(h, t, hk), Equal.trans(Nat, C.low(32n, C.shift(t, v(h))), C.low(Nat.add(t, s), C.shift(t, v(h))), C.shift(t, C.low(s, v(h))), Equal.cong(Nat, Nat, z => C.low(z, C.shift(t, v(h))), 32n, Nat.add(t, s), Equal.sym(Nat, Nat.add(t, s), 32n, hts)), WW.low_shift(t, s, v(h))))
  +a3 = div_p2(l, s, hs)
  +hr = WW.lt_of_fits(t, C.high(s, v(l)), fits_high(s, t, v(l), fits32(s, t, hst, l)))
  +hsum = WW.two_limb_lt(t, s, C.high(s, v(l)), C.low(s, v(h)), hr, WW.low_lt(s, v(h)))
  +x1 = U32.mul(h, X.pow2(t))
  +x2 = U32.div(l, X.pow2(s))
  +es = Equal.trans(Nat, Nat.add(v(x1), v(x2)), Nat.add(C.shift(t, C.low(s, v(h))), C.high(s, v(l))), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), Equal.trans(Nat, Nat.add(v(x1), v(x2)), Nat.add(C.shift(t, C.low(s, v(h))), v(x2)), Nat.add(C.shift(t, C.low(s, v(h))), C.high(s, v(l))), Equal.cong(Nat, Nat, z => Nat.add(z, v(x2)), v(x1), C.shift(t, C.low(s, v(h))), a2), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, C.low(s, v(h))), z), v(x2), C.high(s, v(l)), a3)), N.add_comm(C.shift(t, C.low(s, v(h))), C.high(s, v(l))))
  +hf = L.subst(Nat, z => {C.fits(z, Nat.add(v(x1), v(x2))) == True{} : Bool}, Nat.add(t, s), 32n, hts, WW.fits_of_lt(Nat.add(t, s), Nat.add(v(x1), v(x2)), L.subst(Nat, z => {Nat.is_lt(z, C.pow2(Nat.add(t, s))) == True{} : Bool}, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), Nat.add(v(x1), v(x2)), Equal.sym(Nat, Nat.add(v(x1), v(x2)), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), es), hsum)))
  +ehi = Equal.trans(Nat, v(U32.add(x1, x2)), Nat.add(v(x1), v(x2)), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), WA.add_exact(1n, {==}, x1, x2, hf), es)
  +ev = Equal.trans(Nat, Nat.add(v(U32.mul(l, X.pow2(t))), C.shift(32n, v(U32.add(x1, x2)))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, v(U32.add(x1, x2)))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(U32.add(x1, x2)))), v(U32.mul(l, X.pow2(t))), C.shift(t, C.low(s, v(l))), a1), Equal.cong(Nat, Nat, z => Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, z)), v(U32.add(x1, x2)), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), ehi))
  +hR = WW.limbs_fit(32n, 32n, C.shift(t, C.low(s, v(l))), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), L.subst(Nat, z => {C.fits(z, C.shift(t, C.low(s, v(l)))) == True{} : Bool}, Nat.add(t, s), 32n, hts, WW.fits_of_lt(Nat.add(t, s), C.shift(t, C.low(s, v(l))), L.subst(Nat, z => {Nat.is_lt(C.shift(t, C.low(s, v(l))), z) == True{} : Bool}, C.shift(t, C.pow2(s)), C.pow2(Nat.add(t, s)), WW.shift_pow2(t, s), WW.shift_lt(t, C.low(s, v(l)), C.pow2(s), WW.low_lt(s, v(l)))))), L.subst(Nat, z => {C.fits(z, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))) == True{} : Bool}, Nat.add(t, s), 32n, hts, WW.fits_of_lt(Nat.add(t, s), Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))), hsum)))
  +et = Equal.trans(Nat, C.low(64n, C.shift(t, Nat.add(v(l), C.shift(32n, v(h))))), C.low(64n, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h))))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), Equal.cong(Nat, Nat, z => C.low(64n, z), C.shift(t, Nat.add(v(l), C.shift(32n, v(h)))), Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h)))), shl_eq(t, s, hts, l, h)), Equal.trans(Nat, C.low(64n, Nat.add(Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.shift(64n, C.high(s, v(h))))), C.low(64n, Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h))))))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), WW.low_add_shift(64n, Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.high(s, v(h))), WW.low_fit(64n, Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), hR)))
  Equal.trans(Nat, Nat.add(v(U32.mul(l, X.pow2(t))), C.shift(32n, v(U32.add(x1, x2)))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), C.low(64n, C.shift(t, Nat.add(v(l), C.shift(32n, v(h))))), ev, Equal.sym(Nat, C.low(64n, C.shift(t, Nat.add(v(l), C.shift(32n, v(h))))), Nat.add(C.shift(t, C.low(s, v(l))), C.shift(32n, Nat.add(C.high(s, v(l)), C.shift(t, C.low(s, v(h)))))), et))

def shl_big(+l: U32, +h: U32, +k: Nat, +hge: {Nat.is_le(32n, k) == True{} : Bool}, +hlt: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {SW.value(WU.U64{0, U32.mul(l, X.pow2(Nat.sub(k, 32n)))}) == C.low(64n, C.shift(k, val(l, h))) : Nat}:
  +d = Nat.sub(k, 32n)
  +ek = N.sub_add(k, 32n, hge)
  +hd = L.subst(Nat, z => {Nat.is_lt(d, z) == True{} : Bool}, Nat.sub(64n, 32n), 32n, {==}, WW.sub_lt_sub(k, 64n, 32n, hlt, hge))
  +y = C.shift(d, v(l))
  +w = C.shift(d, v(h))
  +e1 = Equal.trans(Nat, C.shift(k, val(l, h)), C.shift(Nat.add(32n, d), val(l, h)), C.shift(32n, C.shift(d, val(l, h))), Equal.cong(Nat, Nat, z => C.shift(z, val(l, h)), k, Nat.add(32n, d), Equal.sym(Nat, Nat.add(32n, d), k, ek)), WW.shift_comp(32n, d, val(l, h)))
  +e2 = Equal.trans(Nat, C.shift(d, val(l, h)), Nat.add(y, C.shift(d, C.shift(32n, v(h)))), Nat.add(y, C.shift(32n, w)), WW.shift_add(d, v(l), C.shift(32n, v(h))), Equal.cong(Nat, Nat, z => Nat.add(y, z), C.shift(d, C.shift(32n, v(h))), C.shift(32n, w), shift_swap(d, 32n, v(h))))
  +e3 = Equal.trans(Nat, C.shift(32n, Nat.add(y, C.shift(32n, w))), Nat.add(C.shift(32n, y), C.shift(32n, C.shift(32n, w))), Nat.add(C.shift(32n, y), C.shift(64n, w)), WW.shift_add(32n, y, C.shift(32n, w)), Equal.cong(Nat, Nat, z => Nat.add(C.shift(32n, y), z), C.shift(32n, C.shift(32n, w)), C.shift(64n, w), Equal.sym(Nat, C.shift(64n, w), C.shift(32n, C.shift(32n, w)), WW.shift_comp(32n, 32n, w))))
  +e4 = Equal.trans(Nat, C.shift(k, val(l, h)), C.shift(32n, C.shift(d, val(l, h))), Nat.add(C.shift(32n, y), C.shift(64n, w)), e1, Equal.trans(Nat, C.shift(32n, C.shift(d, val(l, h))), C.shift(32n, Nat.add(y, C.shift(32n, w))), Nat.add(C.shift(32n, y), C.shift(64n, w)), Equal.cong(Nat, Nat, z => C.shift(32n, z), C.shift(d, val(l, h)), Nat.add(y, C.shift(32n, w)), e2), e3))
  +e5 = Equal.trans(Nat, C.low(64n, C.shift(k, val(l, h))), C.low(64n, Nat.add(C.shift(32n, y), C.shift(64n, w))), C.shift(32n, C.low(32n, y)), Equal.cong(Nat, Nat, z => C.low(64n, z), C.shift(k, val(l, h)), Nat.add(C.shift(32n, y), C.shift(64n, w)), e4), Equal.trans(Nat, C.low(64n, Nat.add(C.shift(32n, y), C.shift(64n, w))), C.low(64n, C.shift(32n, y)), C.shift(32n, C.low(32n, y)), WW.low_add_shift(64n, C.shift(32n, y), w), WW.low_shift(32n, 32n, y)))
  Equal.trans(Nat, C.shift(32n, v(U32.mul(l, X.pow2(d)))), C.shift(32n, C.low(32n, y)), C.low(64n, C.shift(k, val(l, h))), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(U32.mul(l, X.pow2(d))), C.low(32n, y), mul_p2(l, d, hd)), Equal.sym(Nat, C.low(64n, C.shift(k, val(l, h))), C.shift(32n, C.low(32n, y)), e5))

def shl_c(+l: U32, +h: U32, +k: Nat, +c: Bool, +hc: {Nat.is_lt(k, 32n) == c : Bool}, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {SW.value(X.shl_pick(WU.U64{l, h}, k, c)) == C.low(64n, C.shift(k, val(l, h))) : Nat}:
  match k c:
    case 0n True{}:
      Equal.sym(Nat, C.low(64n, val(l, h)), val(l, h), WW.low_fit(64n, val(l, h), fit64(l, h)))
    case 1n+ +j True{}:
      shl_small(l, h, j, hc)
    case _ False{}:
      shl_big(l, h, k, N.not_lt_le(k, 32n, hc), hk)

def shl_value(+a: WU.U64, +k: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> SW.Shl.value(a, k, hk):
  match a:
    case WU.U64{+l, +h}:
      shl_c(l, h, k, Nat.is_lt(k, 32n), {==}, hk)

# ---- shift right with jamming ----

def or_zero(+p: Nat, +t: Word(p)) -> {Word.or(p, t, WD.mask(p, 0n)) == t : Word(p)}:
  match p t:
    case 0n WNil{}:
      {==}
    case 1n+q WCon{b, s}:
      match b:
        case True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.or(q, s, WD.mask(q, 0n)), s, or_zero(q, s))
        case False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.or(q, s, WD.mask(q, 0n)), s, or_zero(q, s))

def or_t(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def half_bv(+b: Bool, +u: Nat) -> {C.half(Nat.add(S.bit_value(b), Nat.double(u))) == u : Nat}:
  match b:
    case True{}:
      WW.half_dbl(1n, u)
    case False{}:
      WW.half_dbl(0n, u)

# setting bit 0: 1 + 2 half(x)
def or1(+x: U32) -> {v(U32.or(x, 1)) == 1n+Nat.double(C.half(v(x))) : Nat}:
  match x:
    case U32{+w}:
      match w:
        case WCon{+b, +t}:
          +e1 = Equal.cong(Word(31n), Nat, z => v(U32{WCon{True{}, z}}), Word.or(31n, t, WD.mask(31n, 0n)), t, or_zero(31n, t))
          +ev = Equal.trans(Nat, v(U32{WCon{b, t}}), WD.uw(32n, WCon{b, t}), Nat.add(S.bit_value(b), Nat.double(WD.uw(31n, t))), UD.vw(WCon{b, t}), {==})
          +eh = Equal.trans(Nat, C.half(v(U32{WCon{b, t}})), C.half(Nat.add(S.bit_value(b), Nat.double(WD.uw(31n, t)))), WD.uw(31n, t), Equal.cong(Nat, Nat, z => C.half(z), v(U32{WCon{b, t}}), Nat.add(S.bit_value(b), Nat.double(WD.uw(31n, t))), ev), half_bv(b, WD.uw(31n, t)))
          +e0 = Equal.cong(Bool, Nat, z => v(U32{WCon{z, Word.or(31n, t, WD.mask(31n, 0n))}}), Bool.or(b, True{}), True{}, or_t(b))
          Equal.trans(Nat, v(U32{WCon{Bool.or(b, True{}), Word.or(31n, t, WD.mask(31n, 0n))}}), v(U32{WCon{True{}, Word.or(31n, t, WD.mask(31n, 0n))}}), 1n+Nat.double(C.half(v(U32{WCon{b, t}}))), e0, Equal.trans(Nat, v(U32{WCon{True{}, Word.or(31n, t, WD.mask(31n, 0n))}}), v(U32{WCon{True{}, t}}), 1n+Nat.double(C.half(v(U32{WCon{b, t}}))), e1, Equal.trans(Nat, v(U32{WCon{True{}, t}}), 1n+Nat.double(WD.uw(31n, t)), 1n+Nat.double(C.half(v(U32{WCon{b, t}}))), UD.vw(WCon{True{}, t}), Equal.cong(Nat, Nat, z => 1n+Nat.double(z), WD.uw(31n, t), C.half(v(U32{WCon{b, t}})), Equal.sym(Nat, C.half(v(U32{WCon{b, t}})), WD.uw(31n, t), eh)))))

def or0(+x: U32) -> {U32.or(x, 0) == x : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.or(32n, w, WD.mask(32n, 0n)), w, or_zero(32n, w))

def mod2_lt(+q: Nat) -> {Nat.is_lt(Nat.mod(q, 2n), 2n) == True{} : Bool}:
  NR.dm_lt(1n, q)

def jam0_eq(+q: Nat) -> {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.mod(q, 2n)) == q : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.mod(q, 2n)), Nat.add(Nat.mul(Nat.div(q, 2n), 2n), Nat.mod(q, 2n)), q, Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mod(q, 2n)), Nat.mul(2n, Nat.div(q, 2n)), Nat.mul(Nat.div(q, 2n), 2n), NA.mul_comm(2n, Nat.div(q, 2n))), Equal.sym(Nat, q, Nat.add(Nat.mul(Nat.div(q, 2n), 2n), Nat.mod(q, 2n)), NR.dm_eq(1n, q)))

def jam1_eq(+q: Nat) -> {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), 1n) == 1n+Nat.double(C.half(q)) : Nat}:
  +e = Equal.trans(Nat, Nat.mul(2n, Nat.div(q, 2n)), Nat.double(Nat.div(q, 2n)), Nat.double(C.half(q)), Equal.sym(Nat, Nat.double(Nat.div(q, 2n)), Nat.mul(2n, Nat.div(q, 2n)), NA.double_mul(Nat.div(q, 2n))), Equal.cong(Nat, Nat, z => Nat.double(z), Nat.div(q, 2n), C.half(q), Equal.sym(Nat, C.half(q), Nat.div(q, 2n), WA.half_div(q))))
  Equal.trans(Nat, Nat.add(Nat.mul(2n, Nat.div(q, 2n)), 1n), 1n+Nat.mul(2n, Nat.div(q, 2n)), 1n+Nat.double(C.half(q)), WA.plus1(Nat.mul(2n, Nat.div(q, 2n))), Equal.cong(Nat, Nat, z => 1n+z, Nat.mul(2n, Nat.div(q, 2n)), Nat.double(C.half(q)), e))

def jam0_m(+q: Nat, +m: Nat, +hm: {Nat.mod(q, 2n) == m : Nat}, +h2: {Nat.is_lt(m, 2n) == True{} : Bool}) -> {SW.jam(q, 0n) == q : Nat}:
  match m:
    case 0n:
      L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(z, 0n)) == q : Nat}, 0n, Nat.mod(q, 2n), Equal.sym(Nat, Nat.mod(q, 2n), 0n, hm), L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), z) == q : Nat}, Nat.mod(q, 2n), 0n, hm, jam0_eq(q)))
    case 1n:
      L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(z, 0n)) == q : Nat}, 1n, Nat.mod(q, 2n), Equal.sym(Nat, Nat.mod(q, 2n), 1n, hm), L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), z) == q : Nat}, Nat.mod(q, 2n), 1n, hm, jam0_eq(q)))
    case 2n+z:
      Empty.absurd({SW.jam(q, 0n) == q : Nat}, N.lt_zero_absurd(z, h2))

def jam1_k(+q: Nat, +m: Nat, +hm: {Nat.mod(q, 2n) == m : Nat}, +h2: {Nat.is_lt(m, 2n) == True{} : Bool}) -> {SW.jam(q, 1n) == 1n+Nat.double(C.half(q)) : Nat}:
  match m:
    case 0n:
      L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(z, 1n)) == 1n+Nat.double(C.half(q)) : Nat}, 0n, Nat.mod(q, 2n), Equal.sym(Nat, Nat.mod(q, 2n), 0n, hm), jam1_eq(q))
    case 1n:
      L.subst(Nat, z => {Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(z, 1n)) == 1n+Nat.double(C.half(q)) : Nat}, 1n, Nat.mod(q, 2n), Equal.sym(Nat, Nat.mod(q, 2n), 1n, hm), jam1_eq(q))
    case 2n+z:
      Empty.absurd({SW.jam(q, 1n) == 1n+Nat.double(C.half(q)) : Nat}, N.lt_zero_absurd(z, h2))

def min1(+rp: Nat) -> {Nat.min(1n+rp, 1n) == 1n : Nat}:
  match rp:
    case 0n:
      {==}
    case 1n+x:
      {==}

def jam_r1(+q: Nat, +rp: Nat) -> {SW.jam(q, 1n+rp) == SW.jam(q, 1n) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(Nat.mod(q, 2n), z)), Nat.min(1n+rp, 1n), 1n, min1(rp))

def jam1_m(+q: Nat, +rp: Nat) -> {SW.jam(q, 1n+rp) == 1n+Nat.double(C.half(q)) : Nat}:
  Equal.trans(Nat, SW.jam(q, 1n+rp), SW.jam(q, 1n), 1n+Nat.double(C.half(q)), jam_r1(q, rp), jam1_k(q, Nat.mod(q, 2n), {==}, mod2_lt(q)))

def huge_n(+x: Nat) -> {S.bit_value(Bool.not(Nat.is_eq(x, 0n))) == SW.jam(0n, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+n:
      Equal.sym(Nat, SW.jam(0n, 1n+n), 1n, Equal.trans(Nat, SW.jam(0n, 1n+n), SW.jam(0n, 1n), 1n, jam_r1(0n, n), {==}))

def is_eq_add(+l: Nat, +s: Nat) -> {Nat.is_eq(s, Nat.add(l, s)) == Nat.is_eq(l, 0n) : Bool}:
  match l:
    case 0n:
      N.is_eq_refl(s)
    case 1n+ +lp:
      +h = N.le_lt_trans(s, Nat.add(lp, s), 1n+Nat.add(lp, s), L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, Nat.add(s, lp), Nat.add(lp, s), N.add_comm(s, lp), N.le_add_right(s, lp)), N.lt_succ(Nat.add(lp, s)))
      N.is_eq_lt(s, 1n+Nat.add(lp, s), h)

def fits_lek(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}, +hy: {C.fits(k, y) == True{} : Bool}) -> {C.fits(k, x) == True{} : Bool}:
  WW.fits_of_lt(k, x, N.le_lt_trans(x, y, C.pow2(k), h, WW.lt_of_fits(k, y, hy)))

def sj_big(+l: U32, +h: U32, +k: Nat, +hk: {Nat.is_le(64n, k) == True{} : Bool}) -> {SW.value(WU.U64{X.b32(Bool.not(X.is_zero(WU.U64{l, h}))), 0}) == SW.jam(C.high(k, val(l, h)), C.low(k, val(l, h))) : Nat}:
  +va = val(l, h)
  +hf = fits_mono(64n, k, va, hk, fit64(l, h))
  +eh = N.eq_from_is_eq(C.high(k, va), 0n, hf)
  +el = WW.low_fit(k, va, hf)
  +e1 = Equal.trans(Nat, SW.value(WU.U64{X.b32(Bool.not(X.is_zero(WU.U64{l, h}))), 0}), v(X.b32(Bool.not(X.is_zero(WU.U64{l, h})))), S.bit_value(Bool.not(X.is_zero(WU.U64{l, h}))), val0(X.b32(Bool.not(X.is_zero(WU.U64{l, h})))), W64M.b32_v(Bool.not(X.is_zero(WU.U64{l, h}))))
  +e2 = Equal.cong(Bool, Nat, z => S.bit_value(Bool.not(z)), X.is_zero(WU.U64{l, h}), Nat.is_eq(va, 0n), WA.is_zero_value(WU.U64{l, h}))
  +e3 = Equal.trans(Nat, SW.jam(0n, va), SW.jam(C.high(k, va), va), SW.jam(C.high(k, va), C.low(k, va)), Equal.cong(Nat, Nat, z => SW.jam(z, va), 0n, C.high(k, va), Equal.sym(Nat, C.high(k, va), 0n, eh)), Equal.cong(Nat, Nat, z => SW.jam(C.high(k, va), z), va, C.low(k, va), Equal.sym(Nat, C.low(k, va), va, el)))
  Equal.trans(Nat, SW.value(WU.U64{X.b32(Bool.not(X.is_zero(WU.U64{l, h}))), 0}), S.bit_value(Bool.not(Nat.is_eq(va, 0n))), SW.jam(C.high(k, va), C.low(k, va)), Equal.trans(Nat, SW.value(WU.U64{X.b32(Bool.not(X.is_zero(WU.U64{l, h}))), 0}), S.bit_value(Bool.not(X.is_zero(WU.U64{l, h}))), S.bit_value(Bool.not(Nat.is_eq(va, 0n))), e1, e2), Equal.trans(Nat, S.bit_value(Bool.not(Nat.is_eq(va, 0n))), SW.jam(0n, va), SW.jam(C.high(k, va), C.low(k, va)), huge_n(va), e3))

def sj_bit(+l: U32, +h: U32, +k: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {Bool.not(X.eq(X.shl(X.shr(WU.U64{l, h}, k), k), WU.U64{l, h})) == Bool.not(Nat.is_eq(C.low(k, val(l, h)), 0n)) : Bool}:
  +va = val(l, h)
  +q = C.high(k, va)
  +S1 = X.shr(WU.U64{l, h}, k)
  +S2 = X.shl(S1, k)
  eS1 = shr_value(WU.U64{l, h}, k)
  +ev = Equal.sym(Nat, va, Nat.add(C.low(k, va), C.shift(k, q)), WW.low_high(k, va))
  +hle = L.subst(Nat, z => {Nat.is_le(C.shift(k, q), z) == True{} : Bool}, Nat.add(C.shift(k, q), C.low(k, va)), va, Equal.trans(Nat, Nat.add(C.shift(k, q), C.low(k, va)), Nat.add(C.low(k, va), C.shift(k, q)), va, N.add_comm(C.shift(k, q), C.low(k, va)), ev), N.le_add_right(C.shift(k, q), C.low(k, va)))
  sv = shl_value(S1, k, hk)
  +eS2 = Equal.trans(Nat, SW.value(S2), C.low(64n, C.shift(k, SW.value(S1))), C.shift(k, q), sv, Equal.trans(Nat, C.low(64n, C.shift(k, SW.value(S1))), C.low(64n, C.shift(k, q)), C.shift(k, q), Equal.cong(Nat, Nat, z => C.low(64n, C.shift(k, z)), SW.value(S1), q, eS1), WW.low_fit(64n, C.shift(k, q), fits_lek(64n, C.shift(k, q), va, hle, fit64(l, h)))))
  +eq = Equal.trans(Bool, X.eq(S2, WU.U64{l, h}), Nat.is_eq(SW.value(S2), va), Nat.is_eq(C.low(k, va), 0n), WA.eq_value(S2, WU.U64{l, h}), Equal.trans(Bool, Nat.is_eq(SW.value(S2), va), Nat.is_eq(C.shift(k, q), va), Nat.is_eq(C.low(k, va), 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, va), SW.value(S2), C.shift(k, q), eS2), Equal.trans(Bool, Nat.is_eq(C.shift(k, q), va), Nat.is_eq(C.shift(k, q), Nat.add(C.low(k, va), C.shift(k, q))), Nat.is_eq(C.low(k, va), 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(C.shift(k, q), z), va, Nat.add(C.low(k, va), C.shift(k, q)), Equal.sym(Nat, Nat.add(C.low(k, va), C.shift(k, q)), va, ev)), is_eq_add(C.low(k, va), C.shift(k, q)))))
  Equal.cong(Bool, Bool, z => Bool.not(z), X.eq(S2, WU.U64{l, h}), Nat.is_eq(C.low(k, va), 0n), eq)

def sj_c(+l: U32, +h: U32, +k: Nat, +ln: Nat, +hL: {C.low(k, val(l, h)) == ln : Nat}, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {SW.value(X.or_bit(X.shr(WU.U64{l, h}, k), Bool.not(X.eq(X.shl(X.shr(WU.U64{l, h}, k), k), WU.U64{l, h})))) == SW.jam(C.high(k, val(l, h)), C.low(k, val(l, h))) : Nat}:
  match ln:
    case 0n:
      +S1 = X.shr(WU.U64{l, h}, k)
      +q = C.high(k, val(l, h))
      +hb = Equal.trans(Bool, Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})), Bool.not(Nat.is_eq(C.low(k, val(l, h)), 0n)), False{}, sj_bit(l, h, k, hk), Equal.cong(Nat, Bool, z => Bool.not(Nat.is_eq(z, 0n)), C.low(k, val(l, h)), 0n, hL))
      +e1 = Equal.cong(Bool, Nat, z => SW.value(X.or_bit(S1, z)), Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})), False{}, hb)
      +e2 = Equal.trans(Nat, SW.value(X.or_bit(S1, False{})), SW.value(WU.U64{X.lo(S1), X.hi(S1)}), q, Equal.cong(U32, Nat, z => SW.value(WU.U64{z, X.hi(S1)}), U32.or(X.lo(S1), 0), X.lo(S1), or0(X.lo(S1))), Equal.trans(Nat, SW.value(WU.U64{X.lo(S1), X.hi(S1)}), SW.value(S1), q, Equal.sym(Nat, SW.value(S1), SW.value(WU.U64{X.lo(S1), X.hi(S1)}), WA.val_eta(S1)), shr_value(WU.U64{l, h}, k)))
      +e3 = Equal.trans(Nat, SW.jam(q, C.low(k, val(l, h))), SW.jam(q, 0n), q, Equal.cong(Nat, Nat, z => SW.jam(q, z), C.low(k, val(l, h)), 0n, hL), jam0_m(q, Nat.mod(q, 2n), {==}, mod2_lt(q)))
      Equal.trans(Nat, SW.value(X.or_bit(S1, Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})))), q, SW.jam(q, C.low(k, val(l, h))), Equal.trans(Nat, SW.value(X.or_bit(S1, Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})))), SW.value(X.or_bit(S1, False{})), q, e1, e2), Equal.sym(Nat, SW.jam(q, C.low(k, val(l, h))), q, e3))
    case 1n+ +lp:
      +S1 = X.shr(WU.U64{l, h}, k)
      +q = C.high(k, val(l, h))
      +vl = v(X.lo(S1))
      +vh = v(X.hi(S1))
      +hb = Equal.trans(Bool, Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})), Bool.not(Nat.is_eq(C.low(k, val(l, h)), 0n)), True{}, sj_bit(l, h, k, hk), Equal.cong(Nat, Bool, z => Bool.not(Nat.is_eq(z, 0n)), C.low(k, val(l, h)), 1n+lp, hL))
      +e1 = Equal.cong(Bool, Nat, z => SW.value(X.or_bit(S1, z)), Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})), True{}, hb)
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, vh)), v(U32.or(X.lo(S1), 1)), 1n+Nat.double(C.half(vl)), or1(X.lo(S1)))
      +eq = Equal.trans(Nat, q, SW.value(S1), Nat.add(vl, C.shift(32n, vh)), Equal.sym(Nat, SW.value(S1), q, shr_value(WU.U64{l, h}, k)), WA.val_eta(S1))
      +eh = Equal.trans(Nat, C.half(q), C.half(Nat.add(vl, C.shift(32n, vh))), Nat.add(C.half(vl), C.shift(31n, vh)), Equal.cong(Nat, Nat, z => C.half(z), q, Nat.add(vl, C.shift(32n, vh)), eq), WW.half_dbl(vl, C.shift(31n, vh)))
      +e4 = Equal.trans(Nat, SW.jam(q, C.low(k, val(l, h))), SW.jam(q, 1n+lp), 1n+Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), Equal.cong(Nat, Nat, z => SW.jam(q, z), C.low(k, val(l, h)), 1n+lp, hL), Equal.trans(Nat, SW.jam(q, 1n+lp), 1n+Nat.double(C.half(q)), 1n+Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), jam1_m(q, lp), Equal.cong(Nat, Nat, z => 1n+z, Nat.double(C.half(q)), Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), Equal.trans(Nat, Nat.double(C.half(q)), Nat.double(Nat.add(C.half(vl), C.shift(31n, vh))), Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), Equal.cong(Nat, Nat, z => Nat.double(z), C.half(q), Nat.add(C.half(vl), C.shift(31n, vh)), eh), NA.double_add(C.half(vl), C.shift(31n, vh))))))
      Equal.trans(Nat, SW.value(X.or_bit(S1, Bool.not(X.eq(X.shl(S1, k), WU.U64{l, h})))), SW.value(X.or_bit(S1, True{})), SW.jam(q, C.low(k, val(l, h))), e1, Equal.trans(Nat, SW.value(X.or_bit(S1, True{})), 1n+Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), SW.jam(q, C.low(k, val(l, h))), e2, Equal.sym(Nat, SW.jam(q, C.low(k, val(l, h))), 1n+Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh)), e4)))

def sj_top(+l: U32, +h: U32, +k: Nat, +c: Bool, +hc: {Nat.is_le(64n, k) == c : Bool}) -> {SW.value(X.jam_pick(WU.U64{l, h}, k, c)) == SW.jam(C.high(k, val(l, h)), C.low(k, val(l, h))) : Nat}:
  match c:
    case True{}:
      sj_big(l, h, k, hc)
    case False{}:
      sj_c(l, h, k, C.low(k, val(l, h)), {==}, N.not_le_lt(64n, k, hc))

def shr_jam_value(+a: WU.U64, +k: Nat) -> SW.ShrJam.value(a, k):
  match a:
    case WU.U64{+l, +h}:
      sj_top(l, h, k, Nat.is_le(64n, k), {==})
