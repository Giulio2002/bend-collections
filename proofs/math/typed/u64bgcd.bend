import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/natural.bend as NS
import ../../../src/math/generic.bend as G
import ../../../src/math/num.bend as NM
import ../../../src/math/natural.bend as M
import ../../../src/math/instances.bend as I
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ./width.bend as WW
import ./u64laws.bend as UL
import ../natural/proof.bend as NP
import ./bgcdnat.bend as BN
import ./w64div.bend as W64D
import ../u64/u64div.bend as PD
import ./w64mul.bend as W64M
import ./natlight.bend as SR
import ./w64m128.bend as M128
import ./w64add.bend as WA
import ./w64sqrt.bend as W64S
import ../../lib/word.bend as WD
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./u32laws.bend as LW
import ../../lib/u32.bend as U
import ../../../src/math/w64.bend as X

# The binary gcd at U64 (src/math/generic.bend gcd_bin with the U64
# instance) computes the Nat binary gcd of bgcdnat.bend on the values, by
# the U64 instance laws (Half, Odd, Lt, Sub, IsZero, Rem, Add under its
# AddOver test); bgcdnat.bend shows that is M.gcd.

def v(+x: WU.U64) -> Nat:
  SG.u64_val(x)

# ---- values that fit 64 bits ----

def fits_mono(+m: Nat, +n: Nat, +h: {Nat.is_le(m, n) == True{} : Bool}, +hn: {C.fits(64n, n) == True{} : Bool}) -> {C.fits(64n, m) == True{} : Bool}:
  WW.fits_of_lt(64n, m, N.le_lt_trans(m, n, C.pow2(64n), h, WW.lt_of_fits(64n, n, hn)))

def ndbl_ge(k: Nat, +y: Nat) -> {Nat.is_le(y, BN.ndbl(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      N.le_refl(y)
    case 1n+ +j:
      N.le_trans(y, Nat.add(y, y), BN.ndbl(j, Nat.add(y, y)), N.le_add_right(y, y), ndbl_ge(j, Nat.add(y, y)))

# a divisor of 1 + np is at most 1 + np
def dvd_le(+g: Nat, +np: Nat, +k: Nat, +e: {1n+np == Nat.mul(k, g) : Nat}) -> {Nat.is_le(g, 1n+np) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(g, 1n+np) == True{} : Bool}, N.succ_zero(np, e))
    case 1n+kp:
      %Equal.sym(Nat, 1n+np, Nat.mul(1n+kp, g), e) : {Nat.is_le(g, _) == True{} : Bool}
      N.le_add_right(g, Nat.mul(kp, g))

def gcd_fits_d(+x: Nat, +np: Nat, +hy: {C.fits(64n, 1n+np) == True{} : Bool}, d: {Nat.is_le(M.gcd(x, 1n+np), 1n+np) == True{} : Bool}) -> {C.fits(64n, M.gcd(x, 1n+np)) == True{} : Bool}:
  fits_mono(M.gcd(x, 1n+np), 1n+np, d, hy)

def gcd_fits_w(+x: Nat, +np: Nat, +hy: {C.fits(64n, 1n+np) == True{} : Bool}, w: NS.dvd(M.gcd(x, 1n+np), 1n+np)) -> {C.fits(64n, M.gcd(x, 1n+np)) == True{} : Bool}:
  (k, e) = w
  gcd_fits_d(x, np, hy, dvd_le(M.gcd(x, 1n+np), np, k, e))

def gcd_fits(+x: Nat, +y: Nat, +hx: {C.fits(64n, x) == True{} : Bool}, +hy: {C.fits(64n, y) == True{} : Bool}) -> {C.fits(64n, M.gcd(x, y)) == True{} : Bool}:
  match y:
    case 0n:
      hx
    case 1n+np:
      gcd_fits_w(x, np, hy, NP.divides_right(x, 1n+np))

# ---- stripping ----

def sim_strip_go(f: Nat, +x: WU.U64, +o: Bool) -> {v(G.strip_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, (x, o))) == BN.nstrip_go(f, v(x), o) : Nat}:
  match f o:
    case 0n _:
      {==}
    case 1n+g True{}:
      {==}
    case 1n+ +g False{}:
      +h = I.u64_op(NM.Half{x})
      +ih = sim_strip_go(g, h, I.u64_is(NM.Odd{h}))
      +eo = Equal.trans(Bool, I.u64_is(NM.Odd{h}), BN.odd(v(h)), BN.odd(Nat.div(v(x), 2n)), UL.tests_odd(h), Equal.cong(Nat, Bool, t => BN.odd(t), v(h), Nat.div(v(x), 2n), UL.ops_half(x)))
      +e1 = Equal.cong(Nat, Nat, t => BN.nstrip_go(g, t, I.u64_is(NM.Odd{h})), v(h), Nat.div(v(x), 2n), UL.ops_half(x))
      +e2 = Equal.cong(Bool, Nat, t => BN.nstrip_go(g, Nat.div(v(x), 2n), t), I.u64_is(NM.Odd{h}), BN.odd(Nat.div(v(x), 2n)), eo)
      Equal.trans(Nat, v(G.strip_go(~WU.U64, ~I.u64_op, ~I.u64_is, g, (h, I.u64_is(NM.Odd{h})))), BN.nstrip_go(g, v(h), I.u64_is(NM.Odd{h})), BN.nstrip_go(g, Nat.div(v(x), 2n), BN.odd(Nat.div(v(x), 2n))), ih, Equal.trans(Nat, BN.nstrip_go(g, v(h), I.u64_is(NM.Odd{h})), BN.nstrip_go(g, Nat.div(v(x), 2n), I.u64_is(NM.Odd{h})), BN.nstrip_go(g, Nat.div(v(x), 2n), BN.odd(Nat.div(v(x), 2n))), e1, e2))

def sim_strip(+x: WU.U64) -> {v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, x)) == BN.nstrip(v(x)) : Nat}:
  Equal.trans(Nat, v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, x)), BN.nstrip_go(140n, v(x), I.u64_is(NM.Odd{x})), BN.nstrip(v(x)), sim_strip_go(140n, x, I.u64_is(NM.Odd{x})), Equal.cong(Bool, Nat, t => BN.nstrip_go(140n, v(x), t), I.u64_is(NM.Odd{x}), BN.odd(v(x)), UL.tests_odd(x)))

# ---- doubling back ----

def sim_dbl(c: Nat, +x: WU.U64, +hfit: {C.fits(64n, BN.ndbl(c, v(x))) == True{} : Bool}) -> {v(G.dbl(~WU.U64, ~I.u64_op, c, x)) == BN.ndbl(c, v(x)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+ +k:
      +hf2 = fits_mono(Nat.add(v(x), v(x)), BN.ndbl(k, Nat.add(v(x), v(x))), ndbl_ge(k, Nat.add(v(x), v(x))), hfit)
      +hno = Equal.trans(Bool, I.u64_is(NM.AddOver{x, x}), Bool.not(C.fits(64n, Nat.add(v(x), v(x)))), False{}, UL.tests_add_over(x, x), Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, Nat.add(v(x), v(x))), True{}, hf2))
      +s = I.u64_op(NM.Add{x, x})
      +hfit2 = Equal.trans(Bool, C.fits(64n, BN.ndbl(k, v(s))), C.fits(64n, BN.ndbl(k, Nat.add(v(x), v(x)))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, BN.ndbl(k, t)), v(s), Nat.add(v(x), v(x)), UL.ops_add(x, x, hno)), hfit)
      Equal.trans(Nat, v(G.dbl(~WU.U64, ~I.u64_op, k, s)), BN.ndbl(k, v(s)), BN.ndbl(k, Nat.add(v(x), v(x))), sim_dbl(k, s, hfit2), Equal.cong(Nat, Nat, t => BN.ndbl(k, t), v(s), Nat.add(v(x), v(x)), UL.ops_add(x, x, hno)))

# ---- the small pair: Euclid on Nat (both below 2^48) ----

def hv(+l: U32, +h: U32) -> {U32.to_nat(h) == C.high(32n, v(WU.U64{l, h})) : Nat}:
  Equal.sym(Nat, C.high(32n, v(WU.U64{l, h})), U32.to_nat(h), WW.high_u(32n, U32.to_nat(l), U32.to_nat(h), LW.vb(l)))

# 2^16 and 2^16 - 1 as words c: their values are the Nat literals, reached
# over an open unit (a closed U32.to_nat(65536) unfolds in unary)
def kv16(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 16n)} : U32}) -> {U32.to_nat(c) == 65536n : Nat}:
  Equal.trans(Nat, U32.to_nat(c), WD.sc(16n, one), 65536n, PD.pow32(16n, {==}, one, h1, c, hc), Equal.sym(Nat, 65536n, WD.sc(16n, one), W64D.k65536(one, h1)))

def kv15(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.mask(32n, 16n)} : U32}) -> {U32.to_nat(c) == 65535n : Nat}:
  +e = Equal.trans(Nat, 1n+U32.to_nat(c), WD.sc(16n, one), 65536n, W64S.m16(one, h1, c, hc), Equal.sym(Nat, 65536n, WD.sc(16n, one), W64D.k65536(one, h1)))
  N.succ_inj(U32.to_nat(c), 65535n, e)

def fh_c(+l: U32, +h: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 16n)} : U32}, +one: Nat, +h1: {one == 1n : Nat}) -> {U32.is_lt(h, c) == Nat.is_lt(C.high(32n, v(WU.U64{l, h})), 65536n) : Bool}:
  Equal.trans(Bool, U32.is_lt(h, c), Nat.is_lt(U32.to_nat(h), U32.to_nat(c)), Nat.is_lt(C.high(32n, v(WU.U64{l, h})), 65536n), U.is_lt_nat(h, c), Equal.trans(Bool, Nat.is_lt(U32.to_nat(h), U32.to_nat(c)), Nat.is_lt(U32.to_nat(h), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{l, h})), 65536n), Equal.cong(Nat, Bool, z => Nat.is_lt(U32.to_nat(h), z), U32.to_nat(c), 65536n, kv16(one, h1, c, hc)), Equal.cong(Nat, Bool, z => Nat.is_lt(z, 65536n), U32.to_nat(h), C.high(32n, v(WU.U64{l, h})), hv(l, h))))

def fh(+l: U32, +h: U32) -> {U32.is_lt(h, 65536) == Nat.is_lt(C.high(32n, v(WU.U64{l, h})), 65536n) : Bool}:
  fh_c(l, h, 65536, {==}, 1n, {==})

def fzh(+l: U32, +h: U32) -> {U32.is_zero(h) == Nat.is_eq(C.high(32n, v(WU.U64{l, h})), 0n) : Bool}:
  Equal.trans(Bool, U32.is_zero(h), Nat.is_eq(U32.to_nat(h), 0n), Nat.is_eq(C.high(32n, v(WU.U64{l, h})), 0n), LW.zero_nat(h), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), U32.to_nat(h), C.high(32n, v(WU.U64{l, h})), hv(l, h)))

def fl_c(+l: U32, +h: U32, +c: U32, +hc: {c == U32{WD.mask(32n, 16n)} : U32}, +one: Nat, +h1: {one == 1n : Nat}) -> {U32.is_lt(c, l) == Nat.is_lt(65535n, C.low(32n, v(WU.U64{l, h}))) : Bool}:
  +e = WW.low_u(32n, U32.to_nat(l), U32.to_nat(h), LW.vb(l))
  Equal.trans(Bool, U32.is_lt(c, l), Nat.is_lt(U32.to_nat(c), U32.to_nat(l)), Nat.is_lt(65535n, C.low(32n, v(WU.U64{l, h}))), U.is_lt_nat(c, l), Equal.trans(Bool, Nat.is_lt(U32.to_nat(c), U32.to_nat(l)), Nat.is_lt(65535n, U32.to_nat(l)), Nat.is_lt(65535n, C.low(32n, v(WU.U64{l, h}))), Equal.cong(Nat, Bool, z => Nat.is_lt(z, U32.to_nat(l)), U32.to_nat(c), 65535n, kv15(one, h1, c, hc)), Equal.cong(Nat, Bool, z => Nat.is_lt(65535n, z), U32.to_nat(l), C.low(32n, v(WU.U64{l, h})), Equal.sym(Nat, C.low(32n, v(WU.U64{l, h})), U32.to_nat(l), e))))

def fl(+l: U32, +h: U32) -> {U32.is_lt(65535, l) == Nat.is_lt(65535n, C.low(32n, v(WU.U64{l, h}))) : Bool}:
  fl_c(l, h, 65535, {==}, 1n, {==})

# the Small test is nsm on the values
def smv(+a: WU.U64, +d: WU.U64) -> {I.u64_is(NM.Small{a, d}) == BN.nsm(v(a), v(d)) : Bool}:
  match a d:
    case WU.U64{+al, +ah} WU.U64{+dl, +dh}:
      Equal.trans(Bool, Bool.and(Bool.and(U32.is_lt(ah, 65536), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(65535n, C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(z, U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), U32.is_lt(ah, 65536), Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), fh(al, ah)), Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(65535n, C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), z), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), U32.is_lt(dh, 65536), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n), fh(dl, dh)), Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(65535n, C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(z), U32.is_lt(65535, al))), U32.is_zero(ah), Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n), fzh(al, ah)), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), 65536n), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), 65536n)), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), z)), U32.is_lt(65535, al), Nat.is_lt(65535n, C.low(32n, v(WU.U64{al, ah}))), fl(al, ah)))))

# (x 2^16) 2^16 == x 2^32
def s32(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(Nat.mul(x, 65536n), 65536n) == C.shift(32n, x) : Nat}:
  +k = W64D.k65536(one, h1)
  +e1 = PD.mul_pow(one, h1, 16n, x, 65536n, k)
  +e2 = Equal.trans(Nat, Nat.mul(Nat.mul(x, 65536n), 65536n), Nat.mul(WD.sc(16n, x), 65536n), WD.sc(16n, WD.sc(16n, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, 65536n), Nat.mul(x, 65536n), WD.sc(16n, x), e1), PD.mul_pow(one, h1, 16n, WD.sc(16n, x), 65536n, k))
  Equal.trans(Nat, Nat.mul(Nat.mul(x, 65536n), 65536n), WD.sc(16n, WD.sc(16n, x)), C.shift(32n, x), e2, Equal.trans(Nat, WD.sc(16n, WD.sc(16n, x)), WD.sc(32n, x), C.shift(32n, x), W64M.sc_sc(16n, 16n, x), Equal.sym(Nat, C.shift(32n, x), WD.sc(32n, x), W64M.shift_sc(32n, x))))

def n48v(+one: Nat, +h1: {one == 1n : Nat}, +a: WU.U64) -> {X.n48(a) == v(a) : Nat}:
  match a:
    case WU.U64{+l, +h}:
      Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(l), z), Nat.mul(Nat.mul(U32.to_nat(h), 65536n), 65536n), C.shift(32n, U32.to_nat(h)), s32(one, h1, U32.to_nat(h)))

# ---- of48: the words of g < 2^64 (2^16 and 2^32 kept over an open unit) ----

def o48_shl_inv_c(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(C.shift(k, a), C.shift(k, b)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h2 = WW.shift_mono(k, b, a, N.not_lt_le(a, b, hc))
      Empty.absurd({False{} == True{} : Bool}, LW.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(C.shift(k, a), C.shift(k, b)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(k, a), C.shift(k, b)), True{}, h), N.le_not_lt(C.shift(k, a), C.shift(k, b), h2))))

def o48_shl_inv(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(C.shift(k, a), C.shift(k, b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  o48_shl_inv_c(k, a, b, h, Nat.is_lt(a, b), {==})

# a value below 2^32 survives from_nat / to_nat
def tnfn(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_lt(x, C.shift(32n, one)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(x)) == x : Nat}:
  +e = Equal.trans(Nat, C.shift(32n, one), C.shift(32n, 1n), C.pow2(32n), Equal.cong(Nat, Nat, z => C.shift(32n, z), one, 1n, h1), WW.shift_one(32n))
  U.to_nat_from_nat(x, 32n, {==}, L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, C.shift(32n, one), C.pow2(32n), e, hx))

def k16s(+one: Nat, +h1: {one == 1n : Nat}) -> {65536n == C.shift(16n, one) : Nat}:
  Equal.trans(Nat, 65536n, WD.sc(16n, one), C.shift(16n, one), W64D.k65536(one, h1), Equal.sym(Nat, C.shift(16n, one), WD.sc(16n, one), W64M.shift_sc(16n, one)))

# g = (2^16 r2 + r1) + 2^32 h: r1, r2 the low 16-bit digits, h = g div 2^32
def o48_split(+one: Nat, +h1: {one == 1n : Nat}, +g: Nat) -> {Nat.add(Nat.add(C.shift(16n, Nat.mod(Nat.div(g, 65536n), 65536n)), Nat.mod(g, 65536n)), C.shift(32n, Nat.div(Nat.div(g, 65536n), 65536n))) == g : Nat}:
  +q1 = Nat.div(g, 65536n)
  +r1 = Nat.mod(g, 65536n)
  +h = Nat.div(q1, 65536n)
  +r2 = Nat.mod(q1, 65536n)
  +X1 = Nat.add(Nat.mul(Nat.add(Nat.mul(h, 65536n), r2), 65536n), r1)
  +e1 = Equal.trans(Nat, X1, Nat.add(Nat.mul(q1, 65536n), r1), g, Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, 65536n), r1), Nat.add(Nat.mul(h, 65536n), r2), q1, SR.dmq(q1, 65536n, {==})), SR.dmq(g, 65536n, {==}))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(WD.sc(16n, r2), r1), WD.sc(32n, h)), X1, g, Equal.sym(Nat, X1, Nat.add(Nat.add(WD.sc(16n, r2), r1), WD.sc(32n, h)), W64D.x2_eq(one, h1, h, r2, r1)), e1)
  +e3 = Equal.trans(Nat, Nat.add(Nat.add(C.shift(16n, r2), r1), C.shift(32n, h)), Nat.add(Nat.add(WD.sc(16n, r2), r1), C.shift(32n, h)), Nat.add(Nat.add(WD.sc(16n, r2), r1), WD.sc(32n, h)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, r1), C.shift(32n, h)), C.shift(16n, r2), WD.sc(16n, r2), W64M.shift_sc(16n, r2)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(WD.sc(16n, r2), r1), z), C.shift(32n, h), WD.sc(32n, h), W64M.shift_sc(32n, h)))
  Equal.trans(Nat, Nat.add(Nat.add(C.shift(16n, r2), r1), C.shift(32n, h)), Nat.add(Nat.add(WD.sc(16n, r2), r1), WD.sc(32n, h)), g, e3, e2)

# two 16-bit digits make a value below 2^32
def o48_lo_lt(+one: Nat, +h1: {one == 1n : Nat}, +r1: Nat, +r2: Nat, +hr1: {Nat.is_lt(r1, 65536n) == True{} : Bool}, +hr2: {Nat.is_lt(r2, 65536n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(C.shift(16n, r2), r1), C.shift(32n, one)) == True{} : Bool}:
  +S = C.shift(16n, one)
  +k = k16s(one, h1)
  +a1 = L.subst(Nat, z => {Nat.is_lt(r1, z) == True{} : Bool}, 65536n, S, k, hr1)
  +a2 = L.subst(Nat, z => {Nat.is_lt(r2, z) == True{} : Bool}, 65536n, S, k, hr2)
  +b1 = N.lt_add_left(r1, S, C.shift(16n, r2), a1)
  +l1 = N.lt_succ_le_succ(r2, S, a2)
  +l2 = L.subst(Nat, z => {Nat.is_le(z, S) == True{} : Bool}, 1n+r2, Nat.add(r2, one), Equal.trans(Nat, 1n+r2, Nat.add(r2, 1n), Nat.add(r2, one), Equal.sym(Nat, Nat.add(r2, 1n), 1n+r2, WA.plus1(r2)), Equal.cong(Nat, Nat, z => Nat.add(r2, z), 1n, one, Equal.sym(Nat, one, 1n, h1))), l1)
  +c1 = WW.shift_mono(16n, Nat.add(r2, one), S, l2)
  +c2 = L.subst(Nat, z => {Nat.is_le(z, C.shift(16n, S)) == True{} : Bool}, C.shift(16n, Nat.add(r2, one)), Nat.add(C.shift(16n, r2), S), WW.shift_add(16n, r2, one), c1)
  +c3 = L.subst(Nat, z => {Nat.is_le(Nat.add(C.shift(16n, r2), S), z) == True{} : Bool}, C.shift(16n, S), C.shift(32n, one), Equal.sym(Nat, C.shift(32n, one), C.shift(16n, S), WW.shift_comp(16n, 16n, one)), c2)
  N.lt_le_trans(Nat.add(C.shift(16n, r2), r1), Nat.add(C.shift(16n, r2), S), C.shift(32n, one), b1, c3)

# the high word of g < 2^64 is below 2^32
def o48_hi_lt(+one: Nat, +h1: {one == 1n : Nat}, +g: Nat, +hg: {C.fits(64n, g) == True{} : Bool}, +L0: Nat, +h: Nat, +es: {Nat.add(L0, C.shift(32n, h)) == g : Nat}) -> {Nat.is_lt(h, C.shift(32n, one)) == True{} : Bool}:
  +hg64 = WW.lt_one(64n, one, h1, g, hg)
  +s1 = L.subst(Nat, z => {Nat.is_le(C.shift(32n, h), z) == True{} : Bool}, Nat.add(C.shift(32n, h), L0), g, Equal.trans(Nat, Nat.add(C.shift(32n, h), L0), Nat.add(L0, C.shift(32n, h)), g, NA.add_comm(C.shift(32n, h), L0), es), N.le_add_right(C.shift(32n, h), L0))
  +s2 = N.le_lt_trans(C.shift(32n, h), g, C.shift(64n, one), s1, hg64)
  +s3 = L.subst(Nat, z => {Nat.is_lt(C.shift(32n, h), z) == True{} : Bool}, C.shift(64n, one), C.shift(32n, C.shift(32n, one)), WW.shift_comp(32n, 32n, one), s2)
  o48_shl_inv(32n, h, C.shift(32n, one), s3)

# the two words of g < 2^64
def of48v(+one: Nat, +h1: {one == 1n : Nat}, +g: Nat, +hg: {C.fits(64n, g) == True{} : Bool}) -> {v(X.of48(g)) == g : Nat}:
  +r1 = Nat.mod(g, 65536n)
  +r2 = Nat.mod(Nat.div(g, 65536n), 65536n)
  +h = Nat.div(Nat.div(g, 65536n), 65536n)
  +L0 = Nat.add(C.shift(16n, r2), r1)
  +M = Nat.mul(Nat.mul(h, 65536n), 65536n)
  +es = o48_split(one, h1, g)
  +eg = Equal.sym(Nat, Nat.add(C.shift(32n, h), L0), g, Equal.trans(Nat, Nat.add(C.shift(32n, h), L0), Nat.add(L0, C.shift(32n, h)), g, NA.add_comm(C.shift(32n, h), L0), es))
  +eE = Equal.trans(Nat, Nat.sub(g, M), Nat.sub(g, C.shift(32n, h)), Nat.sub(Nat.add(C.shift(32n, h), L0), C.shift(32n, h)), Equal.cong(Nat, Nat, z => Nat.sub(g, z), M, C.shift(32n, h), s32(one, h1, h)), Equal.cong(Nat, Nat, z => Nat.sub(z, C.shift(32n, h)), g, Nat.add(C.shift(32n, h), L0), eg))
  +eL = Equal.trans(Nat, Nat.sub(g, M), Nat.sub(Nat.add(C.shift(32n, h), L0), C.shift(32n, h)), L0, eE, N.add_sub_cancel(C.shift(32n, h), L0))
  +bL = o48_lo_lt(one, h1, r1, r2, SR.dml(g, 65536n, {==}), SR.dml(Nat.div(g, 65536n), 65536n, {==}))
  +bLo = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, L0, Nat.sub(g, M), Equal.sym(Nat, Nat.sub(g, M), L0, eL), bL)
  +bh = o48_hi_lt(one, h1, g, hg, L0, h, es)
  +eLo = Equal.trans(Nat, U32.to_nat(U32.from_nat(Nat.sub(g, M))), Nat.sub(g, M), L0, tnfn(one, h1, Nat.sub(g, M), bLo), eL)
  +f1 = Equal.trans(Nat, Nat.add(U32.to_nat(U32.from_nat(Nat.sub(g, M))), C.shift(32n, U32.to_nat(U32.from_nat(h)))), Nat.add(L0, C.shift(32n, U32.to_nat(U32.from_nat(h)))), Nat.add(L0, C.shift(32n, h)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, U32.to_nat(U32.from_nat(h)))), U32.to_nat(U32.from_nat(Nat.sub(g, M))), L0, eLo), Equal.cong(Nat, Nat, z => Nat.add(L0, C.shift(32n, z)), U32.to_nat(U32.from_nat(h)), h, tnfn(one, h1, h, bh)))
  Equal.trans(Nat, v(X.of48(g)), Nat.add(L0, C.shift(32n, h)), g, f1, es)

# GcdSmall is the gcd
def gsv(+a: WU.U64, +d: WU.U64) -> {v(I.u64_op(NM.GcdSmall{a, d})) == M.gcd(v(a), v(d)) : Nat}:
  +e1 = Equal.trans(Nat, M.gcd(X.n48(a), X.n48(d)), M.gcd(v(a), X.n48(d)), M.gcd(v(a), v(d)), Equal.cong(Nat, Nat, z => M.gcd(z, X.n48(d)), X.n48(a), v(a), n48v(1n, {==}, a)), Equal.cong(Nat, Nat, z => M.gcd(v(a), z), X.n48(d), v(d), n48v(1n, {==}, d)))
  Equal.trans(Nat, v(X.of48(M.gcd(X.n48(a), X.n48(d)))), v(X.of48(M.gcd(v(a), v(d)))), M.gcd(v(a), v(d)), Equal.cong(Nat, Nat, z => v(X.of48(z)), M.gcd(X.n48(a), X.n48(d)), M.gcd(v(a), v(d)), e1), of48v(1n, {==}, M.gcd(v(a), v(d)), gcd_fits(v(a), v(d), M128.fit64(a), M128.fit64(d))))

# ---- the subtraction loop ----

# nbloop with its arguments rewritten
def nbc(+g: Nat, +x: Nat, +y: Nat, +y2: Nat, +z: Bool, +z2: Bool, +w: Bool, +w2: Bool, +ey: {y == y2 : Nat}, +ez: {z == z2 : Bool}, +ew: {w == w2 : Bool}) -> {BN.nbloop(g, x, y, z, w) == BN.nbloop(g, x, y2, z2, w2) : Nat}:
  Equal.trans(Nat, BN.nbloop(g, x, y, z, w), BN.nbloop(g, x, y2, z, w), BN.nbloop(g, x, y2, z2, w2), Equal.cong(Nat, Nat, t => BN.nbloop(g, x, t, z, w), y, y2, ey), Equal.trans(Nat, BN.nbloop(g, x, y2, z, w), BN.nbloop(g, x, y2, z2, w), BN.nbloop(g, x, y2, z2, w2), Equal.cong(Bool, Nat, t => BN.nbloop(g, x, y2, t, w), z, z2, ez), Equal.cong(Bool, Nat, t => BN.nbloop(g, x, y2, z2, t), w, w2, ew)))

def sim_bnx(+g: Nat, +a: WU.U64, +s: WU.U64, ih: @+a2: WU.U64 -> @+d2: WU.U64 -> {v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, (a2, (d2, (I.u64_is(NM.IsZero{d2}), I.u64_is(NM.Small{a2, d2})))))) == BN.nbloop(g, v(a2), v(d2), I.u64_is(NM.IsZero{d2}), I.u64_is(NM.Small{a2, d2})) : Nat}, +lb: Bool, +hl: {I.u64_is(NM.Lt{s, a}) == lb : Bool}) -> {v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, G.bnx2(~WU.U64, ~I.u64_op, ~I.u64_is, a, s, lb))) == BN.nbloop(g, BN.nba(v(a), v(s), lb), BN.nbd(v(a), v(s), lb), BN.iz(BN.nbd(v(a), v(s), lb)), BN.nsm(BN.nba(v(a), v(s), lb), BN.nbd(v(a), v(s), lb))) : Nat}:
  match lb:
    case True{}:
      +hlt = Equal.trans(Bool, Nat.is_lt(v(s), v(a)), I.u64_is(NM.Lt{s, a}), True{}, Equal.sym(Bool, I.u64_is(NM.Lt{s, a}), Nat.is_lt(v(s), v(a)), UL.tests_lt(s, a)), hl)
      +hle = N.lt_le(v(s), v(a), hlt)
      +r = ih(s, I.u64_op(NM.Sub{a, s}))
      +ez = Equal.trans(Bool, I.u64_is(NM.IsZero{I.u64_op(NM.Sub{a, s})}), BN.iz(v(I.u64_op(NM.Sub{a, s}))), BN.iz(Nat.sub(v(a), v(s))), UL.tests_is_zero(I.u64_op(NM.Sub{a, s})), Equal.cong(Nat, Bool, t => BN.iz(t), v(I.u64_op(NM.Sub{a, s})), Nat.sub(v(a), v(s)), UL.ops_sub(a, s, hle)))
      +ew = Equal.trans(Bool, I.u64_is(NM.Small{s, I.u64_op(NM.Sub{a, s})}), BN.nsm(v(s), v(I.u64_op(NM.Sub{a, s}))), BN.nsm(v(s), Nat.sub(v(a), v(s))), smv(s, I.u64_op(NM.Sub{a, s})), Equal.cong(Nat, Bool, t => BN.nsm(v(s), t), v(I.u64_op(NM.Sub{a, s})), Nat.sub(v(a), v(s)), UL.ops_sub(a, s, hle)))
      Equal.trans(Nat, v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, (s, (I.u64_op(NM.Sub{a, s}), (I.u64_is(NM.IsZero{I.u64_op(NM.Sub{a, s})}), I.u64_is(NM.Small{s, I.u64_op(NM.Sub{a, s})})))))), BN.nbloop(g, v(s), v(I.u64_op(NM.Sub{a, s})), I.u64_is(NM.IsZero{I.u64_op(NM.Sub{a, s})}), I.u64_is(NM.Small{s, I.u64_op(NM.Sub{a, s})})), BN.nbloop(g, v(s), Nat.sub(v(a), v(s)), BN.iz(Nat.sub(v(a), v(s))), BN.nsm(v(s), Nat.sub(v(a), v(s)))), r, nbc(g, v(s), v(I.u64_op(NM.Sub{a, s})), Nat.sub(v(a), v(s)), I.u64_is(NM.IsZero{I.u64_op(NM.Sub{a, s})}), BN.iz(Nat.sub(v(a), v(s))), I.u64_is(NM.Small{s, I.u64_op(NM.Sub{a, s})}), BN.nsm(v(s), Nat.sub(v(a), v(s))), UL.ops_sub(a, s, hle), ez, ew))
    case False{}:
      +hge = N.not_lt_le(v(s), v(a), Equal.trans(Bool, Nat.is_lt(v(s), v(a)), I.u64_is(NM.Lt{s, a}), False{}, Equal.sym(Bool, I.u64_is(NM.Lt{s, a}), Nat.is_lt(v(s), v(a)), UL.tests_lt(s, a)), hl))
      +r = ih(a, I.u64_op(NM.Sub{s, a}))
      +ez = Equal.trans(Bool, I.u64_is(NM.IsZero{I.u64_op(NM.Sub{s, a})}), BN.iz(v(I.u64_op(NM.Sub{s, a}))), BN.iz(Nat.sub(v(s), v(a))), UL.tests_is_zero(I.u64_op(NM.Sub{s, a})), Equal.cong(Nat, Bool, t => BN.iz(t), v(I.u64_op(NM.Sub{s, a})), Nat.sub(v(s), v(a)), UL.ops_sub(s, a, hge)))
      +ew = Equal.trans(Bool, I.u64_is(NM.Small{a, I.u64_op(NM.Sub{s, a})}), BN.nsm(v(a), v(I.u64_op(NM.Sub{s, a}))), BN.nsm(v(a), Nat.sub(v(s), v(a))), smv(a, I.u64_op(NM.Sub{s, a})), Equal.cong(Nat, Bool, t => BN.nsm(v(a), t), v(I.u64_op(NM.Sub{s, a})), Nat.sub(v(s), v(a)), UL.ops_sub(s, a, hge)))
      Equal.trans(Nat, v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, (a, (I.u64_op(NM.Sub{s, a}), (I.u64_is(NM.IsZero{I.u64_op(NM.Sub{s, a})}), I.u64_is(NM.Small{a, I.u64_op(NM.Sub{s, a})})))))), BN.nbloop(g, v(a), v(I.u64_op(NM.Sub{s, a})), I.u64_is(NM.IsZero{I.u64_op(NM.Sub{s, a})}), I.u64_is(NM.Small{a, I.u64_op(NM.Sub{s, a})})), BN.nbloop(g, v(a), Nat.sub(v(s), v(a)), BN.iz(Nat.sub(v(s), v(a))), BN.nsm(v(a), Nat.sub(v(s), v(a)))), r, nbc(g, v(a), v(I.u64_op(NM.Sub{s, a})), Nat.sub(v(s), v(a)), I.u64_is(NM.IsZero{I.u64_op(NM.Sub{s, a})}), BN.iz(Nat.sub(v(s), v(a))), I.u64_is(NM.Small{a, I.u64_op(NM.Sub{s, a})}), BN.nsm(v(a), Nat.sub(v(s), v(a))), UL.ops_sub(s, a, hge), ez, ew))

def sim_bloop(f: Nat, +a: WU.U64, +d: WU.U64, +dz: Bool, +sm: Bool, +hsm: {I.u64_is(NM.Small{a, d}) == sm : Bool}) -> {v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, f, (a, (d, (dz, sm))))) == BN.nbloop(f, v(a), v(d), dz, sm) : Nat}:
  match f dz sm:
    case 0n _ _:
      {==}
    case 1n+g True{} _:
      {==}
    case 1n+g False{} True{}:
      gsv(a, d)
    case 1n+ +g False{} False{}:
      +s = G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, d)
      %sim_strip(d) : {v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, G.bnx(~WU.U64, ~I.u64_op, ~I.u64_is, a, s))) == BN.nbloop(g, BN.nba(v(a), _, Nat.is_lt(_, v(a))), BN.nbd(v(a), _, Nat.is_lt(_, v(a))), BN.iz(BN.nbd(v(a), _, Nat.is_lt(_, v(a)))), BN.nsm(BN.nba(v(a), _, Nat.is_lt(_, v(a))), BN.nbd(v(a), _, Nat.is_lt(_, v(a))))) : Nat}
      %UL.tests_lt(s, a) : {v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, g, G.bnx(~WU.U64, ~I.u64_op, ~I.u64_is, a, s))) == BN.nbloop(g, BN.nba(v(a), v(s), _), BN.nbd(v(a), v(s), _), BN.iz(BN.nbd(v(a), v(s), _)), BN.nsm(BN.nba(v(a), v(s), _), BN.nbd(v(a), v(s), _))) : Nat}
      sim_bnx(g, a, s, a2 => d2 => sim_bloop(g, a2, d2, I.u64_is(NM.IsZero{d2}), I.u64_is(NM.Small{a2, d2}), {==}), I.u64_is(NM.Lt{s, a}), {==})

# ---- the exit and the halving ----

def sim_exit(+a: WU.U64, +b: WU.U64, +c: Nat, +hfit: {C.fits(64n, BN.ndbl(c, BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))))) == True{} : Bool}) -> {v(G.dbl(~WU.U64, ~I.u64_op, c, G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}))))))) == BN.ndbl(c, BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b)))) : Nat}:
  +e1 = sim_bloop(140n, G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b, I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}), {==})
  +ex = sim_strip(a)
  +e2 = Equal.cong(Nat, Nat, t => BN.nbloop(140n, t, v(b), I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})), v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a)), BN.nstrip(v(a)), ex)
  +ew = Equal.trans(Bool, I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}), BN.nsm(v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a)), v(b)), BN.nsm(BN.nstrip(v(a)), v(b)), smv(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b), Equal.cong(Nat, Bool, t => BN.nsm(t, v(b)), v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a)), BN.nstrip(v(a)), ex))
  +e3 = nbc(140n, BN.nstrip(v(a)), v(b), v(b), I.u64_is(NM.IsZero{b}), BN.iz(v(b)), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}), BN.nsm(BN.nstrip(v(a)), v(b)), {==}, UL.tests_is_zero(b), ew)
  +eL = Equal.trans(Nat, v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})))))), BN.nbloop(140n, v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a)), v(b), I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})), BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))), e1, Equal.trans(Nat, BN.nbloop(140n, v(G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a)), v(b), I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})), BN.nbloop(140n, BN.nstrip(v(a)), v(b), I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})), BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))), e2, e3))
  +hfit2 = Equal.trans(Bool, C.fits(64n, BN.ndbl(c, v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})))))))), C.fits(64n, BN.ndbl(c, BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, BN.ndbl(c, t)), v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})))))), BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))), eL), hfit)
  Equal.trans(Nat, v(G.dbl(~WU.U64, ~I.u64_op, c, G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}))))))), BN.ndbl(c, v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}))))))), BN.ndbl(c, BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b)))), sim_dbl(c, G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b}))))), hfit2), Equal.cong(Nat, Nat, t => BN.ndbl(c, t), v(G.bloop(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, (G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), (b, (I.u64_is(NM.IsZero{b}), I.u64_is(NM.Small{G.strip(~WU.U64, ~I.u64_op, ~I.u64_is, a), b})))))), BN.nbloop(140n, BN.nstrip(v(a)), v(b), BN.iz(v(b)), BN.nsm(BN.nstrip(v(a)), v(b))), eL))

def sim_tw(f: Nat, +a: WU.U64, +b: WU.U64, +c: Nat, +both: Bool, +hfit: {C.fits(64n, BN.ntw(f, v(a), v(b), c, both)) == True{} : Bool}) -> {v(G.tw(~WU.U64, ~I.u64_op, ~I.u64_is, f, a, b, c, both)) == BN.ntw(f, v(a), v(b), c, both) : Nat}:
  match f both:
    case 0n _:
      sim_exit(a, b, c, hfit)
    case 1n+g False{}:
      sim_exit(a, b, c, hfit)
    case 1n+ +g True{}:
      +eoa = Equal.trans(Bool, I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), BN.odd(v(I.u64_op(NM.Half{a}))), BN.odd(Nat.div(v(a), 2n)), UL.tests_odd(I.u64_op(NM.Half{a})), Equal.cong(Nat, Bool, t => BN.odd(t), v(I.u64_op(NM.Half{a})), Nat.div(v(a), 2n), UL.ops_half(a)))
      +eob = Equal.trans(Bool, I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}), BN.odd(v(I.u64_op(NM.Half{b}))), BN.odd(Nat.div(v(b), 2n)), UL.tests_odd(I.u64_op(NM.Half{b})), Equal.cong(Nat, Bool, t => BN.odd(t), v(I.u64_op(NM.Half{b})), Nat.div(v(b), 2n), UL.ops_half(b)))
      +ee = Equal.trans(Bool, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))), Bool.not(Bool.or(BN.odd(Nat.div(v(a), 2n)), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))), BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n)), Equal.cong(Bool, Bool, t => Bool.not(Bool.or(t, I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))), I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), BN.odd(Nat.div(v(a), 2n)), eoa), Equal.cong(Bool, Bool, t => Bool.not(Bool.or(BN.odd(Nat.div(v(a), 2n)), t)), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}), BN.odd(Nat.div(v(b), 2n)), eob))
      +x1 = Equal.cong(Nat, Nat, t => BN.ntw(g, t, v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), v(I.u64_op(NM.Half{a})), Nat.div(v(a), 2n), UL.ops_half(a))
      +x2 = Equal.cong(Nat, Nat, t => BN.ntw(g, Nat.div(v(a), 2n), t, 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), v(I.u64_op(NM.Half{b})), Nat.div(v(b), 2n), UL.ops_half(b))
      +x3 = Equal.cong(Bool, Nat, t => BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, t), Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))), BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n)), ee)
      +E = Equal.trans(Nat, BN.ntw(g, v(I.u64_op(NM.Half{a})), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n))), x1, Equal.trans(Nat, BN.ntw(g, Nat.div(v(a), 2n), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n))), x2, x3))
      +hfit2 = Equal.trans(Bool, C.fits(64n, BN.ntw(g, v(I.u64_op(NM.Half{a})), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))))), C.fits(64n, BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n)))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.ntw(g, v(I.u64_op(NM.Half{a})), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n))), E), hfit)
      Equal.trans(Nat, v(G.tw(~WU.U64, ~I.u64_op, ~I.u64_is, g, I.u64_op(NM.Half{a}), I.u64_op(NM.Half{b}), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))))), BN.ntw(g, v(I.u64_op(NM.Half{a})), v(I.u64_op(NM.Half{b})), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})})))), BN.ntw(g, Nat.div(v(a), 2n), Nat.div(v(b), 2n), 1n+c, BN.nev2(Nat.div(v(a), 2n), Nat.div(v(b), 2n))), sim_tw(g, I.u64_op(NM.Half{a}), I.u64_op(NM.Half{b}), 1n+c, Bool.not(Bool.or(I.u64_is(NM.Odd{I.u64_op(NM.Half{a})}), I.u64_is(NM.Odd{I.u64_op(NM.Half{b})}))), hfit2), E)

# ---- the entry: one Euclid step, then the loops ----

def sim_bg_b(+a: WU.U64, +b: WU.U64, +bz: Bool, +hfit: {C.fits(64n, BN.nbg_b(v(a), v(b), bz)) == True{} : Bool}) -> {v(G.bg_b(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, bz)) == BN.nbg_b(v(a), v(b), bz) : Nat}:
  match bz:
    case True{}:
      {==}
    case False{}:
      +e = Equal.trans(Bool, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b}))), Bool.not(Bool.or(BN.odd(v(a)), I.u64_is(NM.Odd{b}))), BN.nev2(v(a), v(b)), Equal.cong(Bool, Bool, t => Bool.not(Bool.or(t, I.u64_is(NM.Odd{b}))), I.u64_is(NM.Odd{a}), BN.odd(v(a)), UL.tests_odd(a)), Equal.cong(Bool, Bool, t => Bool.not(Bool.or(BN.odd(v(a)), t)), I.u64_is(NM.Odd{b}), BN.odd(v(b)), UL.tests_odd(b)))
      +x = Equal.cong(Bool, Nat, t => BN.ntw(140n, v(a), v(b), 0n, t), Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b}))), BN.nev2(v(a), v(b)), e)
      +hfit2 = Equal.trans(Bool, C.fits(64n, BN.ntw(140n, v(a), v(b), 0n, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b}))))), C.fits(64n, BN.ntw(140n, v(a), v(b), 0n, BN.nev2(v(a), v(b)))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.ntw(140n, v(a), v(b), 0n, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b})))), BN.ntw(140n, v(a), v(b), 0n, BN.nev2(v(a), v(b))), x), hfit)
      Equal.trans(Nat, v(G.tw(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, a, b, 0n, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b}))))), BN.ntw(140n, v(a), v(b), 0n, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b})))), BN.ntw(140n, v(a), v(b), 0n, BN.nev2(v(a), v(b))), sim_tw(140n, a, b, 0n, Bool.not(Bool.or(I.u64_is(NM.Odd{a}), I.u64_is(NM.Odd{b}))), hfit2), x)

def sim_bg_a(+a: WU.U64, +b: WU.U64, +az: Bool, +hfit: {C.fits(64n, BN.nbg_a(v(a), v(b), az)) == True{} : Bool}) -> {v(G.bg_a(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, az)) == BN.nbg_a(v(a), v(b), az) : Nat}:
  match az:
    case True{}:
      {==}
    case False{}:
      +x = Equal.cong(Bool, Nat, t => BN.nbg_b(v(a), v(b), t), I.u64_is(NM.IsZero{b}), BN.iz(v(b)), UL.tests_is_zero(b))
      +hfit2 = Equal.trans(Bool, C.fits(64n, BN.nbg_b(v(a), v(b), I.u64_is(NM.IsZero{b}))), C.fits(64n, BN.nbg_b(v(a), v(b), BN.iz(v(b)))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.nbg_b(v(a), v(b), I.u64_is(NM.IsZero{b})), BN.nbg_b(v(a), v(b), BN.iz(v(b))), x), hfit)
      Equal.trans(Nat, v(G.bg_b(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, I.u64_is(NM.IsZero{b}))), BN.nbg_b(v(a), v(b), I.u64_is(NM.IsZero{b})), BN.nbg_b(v(a), v(b), BN.iz(v(b))), sim_bg_b(a, b, I.u64_is(NM.IsZero{b}), hfit2), x)

def sim_rb(+a: WU.U64, +b: WU.U64, +bz: Bool, +hbz: {BN.iz(v(b)) == bz : Bool}, +hfit: {C.fits(64n, BN.nrb(v(a), v(b), bz)) == True{} : Bool}) -> {v(G.gcd_rb(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, bz)) == BN.nrb(v(a), v(b), bz) : Nat}:
  match bz:
    case True{}:
      {==}
    case False{}:
      +x1 = Equal.cong(Nat, Nat, t => BN.nbg_a(v(b), t, I.u64_is(NM.IsZero{b})), v(I.u64_op(NM.Rem{a, b})), Nat.mod(v(a), v(b)), UL.ops_rem(a, b, hbz))
      +x2 = Equal.cong(Bool, Nat, t => BN.nbg_a(v(b), Nat.mod(v(a), v(b)), t), I.u64_is(NM.IsZero{b}), BN.iz(v(b)), UL.tests_is_zero(b))
      +E = Equal.trans(Nat, BN.nbg_a(v(b), v(I.u64_op(NM.Rem{a, b})), I.u64_is(NM.IsZero{b})), BN.nbg_a(v(b), Nat.mod(v(a), v(b)), I.u64_is(NM.IsZero{b})), BN.nbg_a(v(b), Nat.mod(v(a), v(b)), BN.iz(v(b))), x1, x2)
      +hfit2 = Equal.trans(Bool, C.fits(64n, BN.nbg_a(v(b), v(I.u64_op(NM.Rem{a, b})), I.u64_is(NM.IsZero{b}))), C.fits(64n, BN.nbg_a(v(b), Nat.mod(v(a), v(b)), BN.iz(v(b)))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.nbg_a(v(b), v(I.u64_op(NM.Rem{a, b})), I.u64_is(NM.IsZero{b})), BN.nbg_a(v(b), Nat.mod(v(a), v(b)), BN.iz(v(b))), E), hfit)
      Equal.trans(Nat, v(G.bg_a(~WU.U64, ~I.u64_op, ~I.u64_is, b, I.u64_op(NM.Rem{a, b}), I.u64_is(NM.IsZero{b}))), BN.nbg_a(v(b), v(I.u64_op(NM.Rem{a, b})), I.u64_is(NM.IsZero{b})), BN.nbg_a(v(b), Nat.mod(v(a), v(b)), BN.iz(v(b))), sim_bg_a(b, I.u64_op(NM.Rem{a, b}), I.u64_is(NM.IsZero{b}), hfit2), E)

def sim_bin(+a: WU.U64, +b: WU.U64, +hfit: {C.fits(64n, BN.nbin(v(a), v(b))) == True{} : Bool}) -> {v(G.gcd_bin(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)) == BN.nbin(v(a), v(b)) : Nat}:
  +x = Equal.cong(Bool, Nat, t => BN.nrb(v(a), v(b), t), I.u64_is(NM.IsZero{b}), BN.iz(v(b)), UL.tests_is_zero(b))
  +hfit2 = Equal.trans(Bool, C.fits(64n, BN.nrb(v(a), v(b), I.u64_is(NM.IsZero{b}))), C.fits(64n, BN.nbin(v(a), v(b))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.nrb(v(a), v(b), I.u64_is(NM.IsZero{b})), BN.nbin(v(a), v(b)), x), hfit)
  Equal.trans(Nat, v(G.gcd_rb(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, I.u64_is(NM.IsZero{b}))), BN.nrb(v(a), v(b), I.u64_is(NM.IsZero{b})), BN.nbin(v(a), v(b)), sim_rb(a, b, I.u64_is(NM.IsZero{b}), Equal.sym(Bool, I.u64_is(NM.IsZero{b}), BN.iz(v(b)), UL.tests_is_zero(b)), hfit2), x)

# ---- gcd at U64 (G.gcd dispatches to gcd_bin: U64 division is software) ----

def gcd_val(+K: Nat, +hK: {K == 64n : Nat}, +a: WU.U64, +b: WU.U64) -> {v(G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)) == M.gcd(v(a), v(b)) : Nat}:
  +hw = Equal.trans(Bool, Nat.is_le(Nat.add(K, K), 139n), Nat.is_le(Nat.add(64n, 64n), 139n), True{}, Equal.cong(Nat, Bool, t => Nat.is_le(Nat.add(t, t), 139n), K, 64n, hK), {==})
  +hw140 = Equal.trans(Bool, Nat.is_le(K, 140n), Nat.is_le(64n, 140n), True{}, Equal.cong(Nat, Bool, t => Nat.is_le(t, 140n), K, 64n, hK), {==})
  +nb = BN.nbin_gcd(K, hw, hw140, v(a), v(b), UL.val_lt(K, hK, b))
  +hfit = Equal.trans(Bool, C.fits(64n, BN.nbin(v(a), v(b))), C.fits(64n, M.gcd(v(a), v(b))), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), BN.nbin(v(a), v(b)), M.gcd(v(a), v(b)), nb), gcd_fits(v(a), v(b), UL.vb(a), UL.vb(b)))
  Equal.trans(Nat, v(G.gcd_bin(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)), BN.nbin(v(a), v(b)), M.gcd(v(a), v(b)), sim_bin(a, b, hfit), nb)
