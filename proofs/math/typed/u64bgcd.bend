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
import ./natfuel.bend as NF
import ../natural/proof.bend as NP
import ./bgcdnat.bend as BN
import ./w64div.bend as W64D
import ../u64/u64div.bend as PD
import ./w64mul.bend as W64M
import ./f64sqr.bend as SR
import ./w64m128.bend as M128
import ./f64sqn.bend as QN
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

def fh(+l: U32, +h: U32) -> {U32.is_lt(h, 65536) == Nat.is_lt(C.high(32n, v(WU.U64{l, h})), U32.to_nat(65536)) : Bool}:
  Equal.trans(Bool, U32.is_lt(h, 65536), Nat.is_lt(U32.to_nat(h), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{l, h})), U32.to_nat(65536)), U.is_lt_nat(h, 65536), Equal.cong(Nat, Bool, z => Nat.is_lt(z, U32.to_nat(65536)), U32.to_nat(h), C.high(32n, v(WU.U64{l, h})), hv(l, h)))

def fzh(+l: U32, +h: U32) -> {U32.is_zero(h) == Nat.is_eq(C.high(32n, v(WU.U64{l, h})), 0n) : Bool}:
  Equal.trans(Bool, U32.is_zero(h), Nat.is_eq(U32.to_nat(h), 0n), Nat.is_eq(C.high(32n, v(WU.U64{l, h})), 0n), LW.zero_nat(h), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), U32.to_nat(h), C.high(32n, v(WU.U64{l, h})), hv(l, h)))

def fl(+l: U32, +h: U32) -> {U32.is_lt(65535, l) == Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{l, h}))) : Bool}:
  +e = WW.low_u(32n, U32.to_nat(l), U32.to_nat(h), LW.vb(l))
  Equal.trans(Bool, U32.is_lt(65535, l), Nat.is_lt(U32.to_nat(65535), U32.to_nat(l)), Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{l, h}))), U.is_lt_nat(65535, l), Equal.cong(Nat, Bool, z => Nat.is_lt(U32.to_nat(65535), z), U32.to_nat(l), C.low(32n, v(WU.U64{l, h})), Equal.sym(Nat, C.low(32n, v(WU.U64{l, h})), U32.to_nat(l), e)))

# the Small test is nsm on the values
def smv(+a: WU.U64, +d: WU.U64) -> {I.u64_is(NM.Small{a, d}) == BN.nsm(v(a), v(d)) : Bool}:
  match a d:
    case WU.U64{+al, +ah} WU.U64{+dl, +dh}:
      Equal.trans(Bool, Bool.and(Bool.and(U32.is_lt(ah, 65536), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(z, U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), U32.is_lt(ah, 65536), Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), fh(al, ah)), Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), U32.is_lt(dh, 65536)), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), z), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), U32.is_lt(dh, 65536), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536)), fh(dl, dh)), Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(U32.is_zero(ah)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), U32.is_lt(65535, al))), Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{al, ah}))))), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(z), U32.is_lt(65535, al))), U32.is_zero(ah), Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n), fzh(al, ah)), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(C.high(32n, v(WU.U64{al, ah})), U32.to_nat(65536)), Nat.is_lt(C.high(32n, v(WU.U64{dl, dh})), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, v(WU.U64{al, ah})), 0n)), z)), U32.is_lt(65535, al), Nat.is_lt(U32.to_nat(65535), C.low(32n, v(WU.U64{al, ah}))), fl(al, ah)))))

# (x 2^16) 2^16 == x 2^32
def s32(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(Nat.mul(x, Nat.mul(256n, 256n)), Nat.mul(256n, 256n)) == C.shift(32n, x) : Nat}:
  +k = W64D.k65536(one, h1)
  +e1 = PD.mul_pow(one, h1, 16n, x, Nat.mul(256n, 256n), k)
  +e2 = Equal.trans(Nat, Nat.mul(Nat.mul(x, Nat.mul(256n, 256n)), Nat.mul(256n, 256n)), Nat.mul(WD.sc(16n, x), Nat.mul(256n, 256n)), WD.sc(16n, WD.sc(16n, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, Nat.mul(256n, 256n)), Nat.mul(x, Nat.mul(256n, 256n)), WD.sc(16n, x), e1), PD.mul_pow(one, h1, 16n, WD.sc(16n, x), Nat.mul(256n, 256n), k))
  Equal.trans(Nat, Nat.mul(Nat.mul(x, Nat.mul(256n, 256n)), Nat.mul(256n, 256n)), WD.sc(16n, WD.sc(16n, x)), C.shift(32n, x), e2, Equal.trans(Nat, WD.sc(16n, WD.sc(16n, x)), WD.sc(32n, x), C.shift(32n, x), W64M.sc_sc(16n, 16n, x), Equal.sym(Nat, C.shift(32n, x), WD.sc(32n, x), W64M.shift_sc(32n, x))))

def n48v(+one: Nat, +h1: {one == 1n : Nat}, +a: WU.U64) -> {X.n48(a) == v(a) : Nat}:
  match a:
    case WU.U64{+l, +h}:
      Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(l), z), Nat.mul(Nat.mul(U32.to_nat(h), Nat.mul(256n, 256n)), Nat.mul(256n, 256n)), C.shift(32n, U32.to_nat(h)), s32(one, h1, U32.to_nat(h)))

def b2v(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)) == C.shift(32n, one) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(one, Nat.mul(256n, 256n)), Nat.mul(256n, 256n)), C.shift(32n, one), Equal.cong(Nat, Nat, z => Nat.mul(z, Nat.mul(256n, 256n)), Nat.mul(256n, 256n), Nat.mul(one, Nat.mul(256n, 256n)), L.subst(Nat, o => {Nat.mul(256n, 256n) == Nat.mul(o, Nat.mul(256n, 256n)) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), Equal.sym(Nat, Nat.mul(1n, Nat.mul(256n, 256n)), Nat.mul(256n, 256n), QN.mul1(Nat.mul(256n, 256n))))), s32(one, h1, one))

# the two words of g < 2^64
def of48v(+one: Nat, +h1: {one == 1n : Nat}, +g: Nat, +hg: {C.fits(64n, g) == True{} : Bool}) -> {v(X.of48(g)) == g : Nat}:
  +P = C.shift(32n, one)
  +eB = b2v(one, h1)
  +eP = Equal.trans(Nat, P, C.shift(32n, 1n), C.pow2(32n), L.subst(Nat, o => {C.shift(32n, o) == C.shift(32n, 1n) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}), WW.shift_one(32n))
  +hP = N.lt_le_trans(0n, 1n, P, {==}, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, C.pow2(32n), P, Equal.sym(Nat, P, C.pow2(32n), eP), N.pow2_pos(32n)))
  +dq = Nat.div(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))
  +md = Nat.mod(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))
  +hD = L.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, P, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Equal.sym(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, eB), hP)
  +edm = SR.dmq(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), hD)
  +hm0 = SR.dml(g, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), hD)
  +hm = L.subst(Nat, z => {Nat.is_lt(md, z) == True{} : Bool}, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), C.pow2(32n), Equal.trans(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, C.pow2(32n), eB, eP), hm0)
  +hg64 = WW.lt_of_fits(64n, g, hg)
  +esq = Equal.trans(Nat, Nat.mul(Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), Nat.mul(C.pow2(32n), C.pow2(32n)), C.pow2(64n), Equal.trans(Nat, Nat.mul(Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), Nat.mul(C.pow2(32n), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), Nat.mul(C.pow2(32n), C.pow2(32n)), Equal.cong(Nat, Nat, z => Nat.mul(z, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), C.pow2(32n), Equal.trans(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, C.pow2(32n), eB, eP)), Equal.cong(Nat, Nat, z => Nat.mul(C.pow2(32n), z), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), C.pow2(32n), Equal.trans(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, C.pow2(32n), eB, eP))), WW.pow2_sq(32n))
  +h1d = N.le_lt_trans(Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), g, Nat.mul(Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), L.subst(Nat, z => {Nat.is_le(Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), z) == True{} : Bool}, Nat.add(Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), md), g, edm, N.le_add_right(Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), md)), L.subst(Nat, z => {Nat.is_lt(g, z) == True{} : Bool}, C.pow2(64n), Nat.mul(Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), Equal.sym(Nat, Nat.mul(Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), C.pow2(64n), esq), hg64))
  +hdq0 = W64D.lt_cancel_mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), h1d)
  +hdq = L.subst(Nat, z => {Nat.is_lt(dq, z) == True{} : Bool}, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), C.pow2(32n), Equal.trans(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, C.pow2(32n), eB, eP), hdq0)
  +e1 = U.to_nat_from_nat(md, 32n, {==}, hm)
  +e2 = U.to_nat_from_nat(dq, 32n, {==}, hdq)
  +e3 = Equal.trans(Nat, C.shift(32n, dq), Nat.mul(dq, P), Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), WW.shift_mul_one(32n, one, h1, dq), Equal.cong(Nat, Nat, z => Nat.mul(dq, z), P, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), Equal.sym(Nat, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)), P, eB)))
  +e4 = Equal.trans(Nat, Nat.add(md, C.shift(32n, dq)), Nat.add(md, Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))), g, Equal.cong(Nat, Nat, z => Nat.add(md, z), C.shift(32n, dq), Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), e3), Equal.trans(Nat, Nat.add(md, Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))), Nat.add(Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n))), md), g, NA.add_comm(md, Nat.mul(dq, Nat.mul(Nat.mul(256n, 256n), Nat.mul(256n, 256n)))), edm))
  Equal.trans(Nat, v(X.of48(g)), Nat.add(md, C.shift(32n, U32.to_nat(U32.from_nat(dq)))), g, Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, U32.to_nat(U32.from_nat(dq)))), U32.to_nat(U32.from_nat(md)), md, e1), Equal.trans(Nat, Nat.add(md, C.shift(32n, U32.to_nat(U32.from_nat(dq)))), Nat.add(md, C.shift(32n, dq)), g, Equal.cong(Nat, Nat, z => Nat.add(md, C.shift(32n, z)), U32.to_nat(U32.from_nat(dq)), dq, e2), e4))

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
