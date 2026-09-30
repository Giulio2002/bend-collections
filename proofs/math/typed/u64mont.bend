import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./w64mul.bend as W64M
import ./w64sqrt.bend as W64S
import ./w64m128.bend as M128
import ./w64dm.bend as DM
import ./f64sqa.bend as AQ
import ./montnat.bend as MN
import ./w64dmrem.bend as DR
import ../../lib/u32.bend as U
import ../u64/u64div.bend as PD
import ./w64mm.bend as MM
import ../../../src/math/natural.bend as M
import ./f64sqn.bend as QN
import ../natural/sqrtn.bend as SQ2

# src/math/w64.bend's Montgomery multiplication: redc(t) for t < m^2 is
# t / 2^64 mod m, so mont(a, b) 2^64 == a b (mod m) with mont(a, b) < m.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def b32v(c: Bool) -> {v(X.b32(c)) == S.bit_value(c) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

# shift(k, a) < shift(k, b) gives a < b
def shl_inv_c(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(C.shift(k, a), C.shift(k, b)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h2 = WW.shift_mono(k, b, a, N.not_lt_le(a, b, hc))
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(C.shift(k, a), C.shift(k, b)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(k, a), C.shift(k, b)), True{}, h), N.le_not_lt(C.shift(k, a), C.shift(k, b), h2))))

def shl_inv(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(C.shift(k, a), C.shift(k, b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  shl_inv_c(k, a, b, h, Nat.is_lt(a, b), {==})

# the all-ones word is 2^64 - 1
def ones_v(+one: Nat, +h1: {one == 1n : Nat}, +w: U32, +pw: {w == U32{WD.mask(32n, 32n)} : U32}) -> {1n+SW.value(WU.U64{w, w}) == C.shift(64n, one) : Nat}:
  +e1 = Equal.trans(Nat, 1n+v(w), WD.sc(32n, one), C.shift(32n, one), W64S.mask_v(32n, {==}, one, h1, w, pw), Equal.sym(Nat, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one)))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(w))), 1n+v(w), C.shift(32n, one), e1)
  # 2^32 * (1 + v(w)) never appears: under a closed 2^32 shift, 1 + v(w) is
  # one + v(w), which the checker cannot unfold into 2^32 successors
  +q = L.subst(Nat, o => {Nat.add(o, v(w)) == 1n+v(w) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +e1o = Equal.trans(Nat, Nat.add(one, v(w)), 1n+v(w), C.shift(32n, one), q, e1)
  +e3 = Equal.sym(Nat, C.shift(32n, Nat.add(one, v(w))), Nat.add(C.shift(32n, one), C.shift(32n, v(w))), WW.shift_add(32n, one, v(w)))
  +e5 = Equal.cong(Nat, Nat, z => C.shift(32n, z), Nat.add(one, v(w)), C.shift(32n, one), e1o)
  +f2 = Equal.sym(Nat, C.shift(64n, one), C.shift(32n, C.shift(32n, one)), WW.shift_comp(32n, 32n, one))
  +f3 = Equal.trans(Nat, C.shift(32n, Nat.add(one, v(w))), C.shift(32n, C.shift(32n, one)), C.shift(64n, one), e5, f2)
  +f4 = Equal.trans(Nat, Nat.add(C.shift(32n, one), C.shift(32n, v(w))), C.shift(32n, Nat.add(one, v(w))), C.shift(64n, one), e3, f3)
  Equal.trans(Nat, 1n+SW.value(WU.U64{w, w}), Nat.add(C.shift(32n, one), C.shift(32n, v(w))), C.shift(64n, one), e2, f4)

# the full product's two words
def m128v(+p: WU.U64, +q: WU.U64) -> {Nat.add(SW.value(X.pfst(X.mul128(p, q))), C.shift(64n, SW.value(X.psnd(X.mul128(p, q))))) == Nat.mul(SW.value(p), SW.value(q)) : Nat}:
  match p q:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      M128.m128_value(al, ah, bl, bh)


# sub_if: r < 2 m gives r mod m
def sif_c(+bp: Nat, +m: WU.U64, +r: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hr: {Nat.is_lt(SW.value(r), Nat.add(1n+bp, 1n+bp)) == True{} : Bool}, +c: Bool, +hc: {X.le(m, r) == c : Bool}) -> {SW.value(X.sub_if(r, m, c)) == Nat.mod(SW.value(r), 1n+bp) : Nat}:
  match c:
    case True{}:
      +hle0 = Equal.trans(Bool, Nat.is_le(SW.value(m), SW.value(r)), X.le(m, r), True{}, Equal.sym(Bool, X.le(m, r), Nat.is_le(SW.value(m), SW.value(r)), WA.le_value(m, r)), hc)
      +hle = L.subst(Nat, z => {Nat.is_le(z, SW.value(r)) == True{} : Bool}, SW.value(m), 1n+bp, hM, hle0)
      +es = Equal.trans(Nat, SW.value(X.sub(r, m)), Nat.sub(SW.value(r), SW.value(m)), Nat.sub(SW.value(r), 1n+bp), WA.sub_value(r, m, hle0), Equal.cong(Nat, Nat, z => Nat.sub(SW.value(r), z), SW.value(m), 1n+bp, hM))
      +x = Nat.sub(SW.value(r), 1n+bp)
      +hx = N.sub_lt(SW.value(r), 1n+bp, 1n+bp, hle, hr)
      +er = Equal.trans(Nat, Nat.add(Nat.mul(1n, 1n+bp), x), Nat.add(1n+bp, x), SW.value(r), Equal.cong(Nat, Nat, z => Nat.add(z, x), Nat.mul(1n, 1n+bp), 1n+bp, QN.mul1(1n+bp)), N.sub_add(SW.value(r), 1n+bp, hle))
      +em = Equal.trans(Nat, Nat.mod(SW.value(r), 1n+bp), Nat.mod(Nat.add(Nat.mul(1n, 1n+bp), x), 1n+bp), x, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), SW.value(r), Nat.add(Nat.mul(1n, 1n+bp), x), Equal.sym(Nat, Nat.add(Nat.mul(1n, 1n+bp), x), SW.value(r), er)), NR.mod_of(1n, bp, x, hx))
      Equal.trans(Nat, SW.value(X.sub(r, m)), x, Nat.mod(SW.value(r), 1n+bp), es, Equal.sym(Nat, Nat.mod(SW.value(r), 1n+bp), x, em))
    case False{}:
      +hle0 = Equal.trans(Bool, Nat.is_le(SW.value(m), SW.value(r)), X.le(m, r), False{}, Equal.sym(Bool, X.le(m, r), Nat.is_le(SW.value(m), SW.value(r)), WA.le_value(m, r)), hc)
      +hl = L.subst(Nat, z => {Nat.is_lt(SW.value(r), z) == True{} : Bool}, SW.value(m), 1n+bp, hM, N.not_le_lt(SW.value(m), SW.value(r), hle0))
      Equal.sym(Nat, Nat.mod(SW.value(r), 1n+bp), SW.value(r), NR.mod_of(0n, bp, SW.value(r), hl))

def sif(+bp: Nat, +m: WU.U64, +r: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hr: {Nat.is_lt(SW.value(r), Nat.add(1n+bp, 1n+bp)) == True{} : Bool}) -> {SW.value(X.redc_r(m, r)) == Nat.mod(SW.value(r), 1n+bp) : Nat}:
  sif_c(bp, m, r, hM, hr, X.le(m, r), {==})

def swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), NA.add_assoc(a, b, Nat.add(c, d)), Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), NA.add_swap(b, c, d)), Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), NA.add_assoc(a, c, Nat.add(b, d)))))


# the low words of t + u m cancel: tl + pl == 2^64 carry
def rp_low(+one: Nat, +bp: Nat, +tl: WU.U64, +mp: WU.U64, +pl: WU.U64, +ph: WU.U64, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}) -> {Nat.add(SW.value(tl), SW.value(pl)) == C.shift(64n, S.bit_value(X.add_over(tl, pl))) : Nat}:
  +epl = Equal.trans(Nat, C.low(64n, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), C.low(64n, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), SW.value(pl), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp), Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), Equal.sym(Nat, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp), eP)), WW.low_u(64n, SW.value(pl), SW.value(ph), DM.fit64(pl)))
  +e0 = Equal.trans(Nat, C.low(64n, Nat.add(SW.value(tl), SW.value(pl))), C.low(64n, Nat.add(SW.value(tl), C.low(64n, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)))), 0n, Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(SW.value(tl), z)), SW.value(pl), C.low(64n, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Equal.sym(Nat, C.low(64n, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), SW.value(pl), epl)), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(tl), C.low(64n, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)))), C.low(64n, Nat.add(SW.value(tl), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp))), 0n, MN.low_addlow(64n, SW.value(tl), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(tl), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp))), C.low(64n, Nat.add(SW.value(tl), Nat.mul(C.low(64n, Nat.mul(SW.value(tl), SW.value(mp))), 1n+bp))), 0n, Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(SW.value(tl), Nat.mul(z, 1n+bp))), SW.value(X.mul(tl, mp)), C.low(64n, Nat.mul(SW.value(tl), SW.value(mp))), WA.mul_value(tl, mp)), MN.redc0(64n, one, SW.value(tl), 1n+bp, SW.value(mp), hinv))))
  +ea = Equal.trans(Nat, SW.value(X.add(tl, pl)), C.low(64n, Nat.add(SW.value(tl), SW.value(pl))), 0n, WA.add_value(tl, pl), e0)
  Equal.trans(Nat, Nat.add(SW.value(tl), SW.value(pl)), Nat.add(SW.value(X.add(tl, pl)), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), C.shift(64n, S.bit_value(X.add_over(tl, pl))), M128.add_split(tl, pl), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(64n, S.bit_value(X.add_over(tl, pl)))), SW.value(X.add(tl, pl)), 0n, ea))

# 2^64 r' == t + u m for r' = th + ph + carry
def rp_eq(+one: Nat, +bp: Nat, +tl: WU.U64, +th: WU.U64, +mp: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}) -> {C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))) == Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)) : Nat}:
  Equal.trans(Nat, C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), Nat.add(C.shift(64n, Nat.add(SW.value(th), SW.value(ph))), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), WW.shift_add(64n, Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Equal.trans(Nat, Nat.add(C.shift(64n, Nat.add(SW.value(th), SW.value(ph))), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), Nat.add(Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph))), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(64n, S.bit_value(X.add_over(tl, pl)))), C.shift(64n, Nat.add(SW.value(th), SW.value(ph))), Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph))), WW.shift_add(64n, SW.value(th), SW.value(ph))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph))), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), Nat.add(C.shift(64n, S.bit_value(X.add_over(tl, pl))), Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), NA.add_comm(Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph))), C.shift(64n, S.bit_value(X.add_over(tl, pl)))), Equal.trans(Nat, Nat.add(C.shift(64n, S.bit_value(X.add_over(tl, pl))), Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph)))), Nat.add(Nat.add(SW.value(tl), SW.value(pl)), Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph)))), C.shift(64n, S.bit_value(X.add_over(tl, pl))), Nat.add(SW.value(tl), SW.value(pl)), Equal.sym(Nat, Nat.add(SW.value(tl), SW.value(pl)), C.shift(64n, S.bit_value(X.add_over(tl, pl))), rp_low(one, bp, tl, mp, pl, ph, eP, hinv))), Equal.trans(Nat, Nat.add(Nat.add(SW.value(tl), SW.value(pl)), Nat.add(C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph)))), Nat.add(Nat.add(SW.value(tl), C.shift(64n, SW.value(th))), Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), swap4(SW.value(tl), SW.value(pl), C.shift(64n, SW.value(th)), C.shift(64n, SW.value(ph))), Equal.trans(Nat, Nat.add(Nat.add(SW.value(tl), C.shift(64n, SW.value(th))), Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), Nat.add(T, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), Nat.add(SW.value(tl), C.shift(64n, SW.value(th))), T, eT), Equal.cong(Nat, Nat, z => Nat.add(T, z), Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp), eP)))))))

# r' < 2 m, for t < m^2 and m < 2^63
# rp_lt over b = 1 + bp: with the literal successor, 2^64 * (1 + bp) would
# unfold into 2^64 successors in the checker
def rp_lt_g(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, +mp: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +hT: {Nat.is_lt(T, Nat.mul(b, b)) == True{} : Bool}, +h63: {Nat.is_lt(b, C.shift(63n, one)) == True{} : Bool}, +er: {C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))) == Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), b)) : Nat}) -> {Nat.is_lt(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Nat.add(b, b)) == True{} : Bool}:
  +a1 = AQ.mle2(b, b, b, C.shift(63n, one), N.le_refl(b), N.lt_le(b, C.shift(63n, one), h63))
  +a2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(b, b), z) == True{} : Bool}, Nat.mul(b, C.shift(63n, one)), C.shift(63n, b), Equal.sym(Nat, C.shift(63n, b), Nat.mul(b, C.shift(63n, one)), WW.shift_mul_one(63n, one, h1, b)), a1)
  +a3 = N.le_trans(Nat.mul(b, b), C.shift(63n, b), C.shift(64n, b), a2, L.subst(Nat, z => {Nat.is_le(C.shift(63n, b), z) == True{} : Bool}, Nat.add(C.shift(63n, b), C.shift(63n, b)), C.shift(64n, b), Equal.sym(Nat, C.shift(64n, b), Nat.add(C.shift(63n, b), C.shift(63n, b)), NA.double_self(C.shift(63n, b))), N.le_add_right(C.shift(63n, b), C.shift(63n, b))))
  +hT2 = N.lt_le_trans(T, Nat.mul(b, b), C.shift(64n, b), hT, a3)
  +hU = WW.lt_one(64n, one, h1, SW.value(X.mul(tl, mp)), L.subst(Nat, z => {C.fits(64n, z) == True{} : Bool}, C.low(64n, Nat.mul(SW.value(tl), SW.value(mp))), SW.value(X.mul(tl, mp)), Equal.sym(Nat, SW.value(X.mul(tl, mp)), C.low(64n, Nat.mul(SW.value(tl), SW.value(mp))), WA.mul_value(tl, mp)), WW.low_fits(64n, Nat.mul(SW.value(tl), SW.value(mp)))))
  +b1 = AQ.mle2(1n+SW.value(X.mul(tl, mp)), C.shift(64n, one), b, b, N.lt_succ_le_succ(SW.value(X.mul(tl, mp)), C.shift(64n, one), hU), N.le_refl(b))
  +b2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(1n+SW.value(X.mul(tl, mp)), b), z) == True{} : Bool}, Nat.mul(C.shift(64n, one), b), C.shift(64n, b), Equal.trans(Nat, Nat.mul(C.shift(64n, one), b), Nat.mul(b, C.shift(64n, one)), C.shift(64n, b), NA.mul_comm(C.shift(64n, one), b), Equal.sym(Nat, C.shift(64n, b), Nat.mul(b, C.shift(64n, one)), WW.shift_mul_one(64n, one, h1, b))), b1)
  +b3 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(SW.value(X.mul(tl, mp)), b), z) == True{} : Bool}, Nat.add(Nat.mul(SW.value(X.mul(tl, mp)), b), b), Nat.add(b, Nat.mul(SW.value(X.mul(tl, mp)), b)), NA.add_comm(Nat.mul(SW.value(X.mul(tl, mp)), b), b), DM.lt_add_pos(Nat.mul(SW.value(X.mul(tl, mp)), b), b, hb))
  +hUM = N.lt_le(Nat.mul(SW.value(X.mul(tl, mp)), b), C.shift(64n, b), N.lt_le_trans(Nat.mul(SW.value(X.mul(tl, mp)), b), Nat.mul(1n+SW.value(X.mul(tl, mp)), b), C.shift(64n, b), b3, b2))
  +c1 = SQ2.le_add2(1n+T, C.shift(64n, b), Nat.mul(SW.value(X.mul(tl, mp)), b), C.shift(64n, b), N.lt_succ_le_succ(T, C.shift(64n, b), hT2), hUM)
  +c2 = N.succ_le_lt(Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), b)), Nat.add(C.shift(64n, b), C.shift(64n, b)), c1)
  +c3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), b)), z) == True{} : Bool}, Nat.add(C.shift(64n, b), C.shift(64n, b)), C.shift(64n, Nat.add(b, b)), Equal.sym(Nat, C.shift(64n, Nat.add(b, b)), Nat.add(C.shift(64n, b), C.shift(64n, b)), WW.shift_add(64n, b, b)), c2)
  +c4 = L.subst(Nat, z => {Nat.is_lt(z, C.shift(64n, Nat.add(b, b))) == True{} : Bool}, Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), b)), C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), Equal.sym(Nat, C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), b)), er), c3)
  shl_inv(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Nat.add(b, b), c4)

def rp_lt(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +tl: WU.U64, +th: WU.U64, +mp: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Nat.add(1n+bp, 1n+bp)) == True{} : Bool}:
  rp_lt_g(one, h1, 1n+bp, {==}, tl, th, mp, pl, ph, T, hT, h63, rp_eq(one, bp, tl, th, mp, pl, ph, T, eT, eP, hinv))


# a < b and c > 0 give a c < b c
def lt_mul(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}, +hc: {Nat.is_lt(0n, c) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  +h1 = AQ.mle2(1n+a, b, c, c, N.lt_succ_le_succ(a, b, h), N.le_refl(c))
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(a, c), z) == True{} : Bool}, Nat.add(Nat.mul(a, c), c), Nat.add(c, Nat.mul(a, c)), NA.add_comm(Nat.mul(a, c), c), DM.lt_add_pos(Nat.mul(a, c), c, hc))
  N.lt_le_trans(Nat.mul(a, c), Nat.mul(1n+a, c), Nat.mul(b, c), h2, h1)

# m + m < 2^64
def mm64(+one: Nat, +bp: Nat, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(1n+bp, 1n+bp), C.shift(64n, one)) == True{} : Bool}:
  +h = N.lt_le_trans(Nat.add(1n+bp, 1n+bp), Nat.add(C.shift(63n, one), 1n+bp), Nat.add(C.shift(63n, one), C.shift(63n, one)), N.lt_add_r2(1n+bp, C.shift(63n, one), 1n+bp, h63), N.le_add_left(1n+bp, C.shift(63n, one), C.shift(63n, one), N.lt_le(1n+bp, C.shift(63n, one), h63)))
  L.subst(Nat, z => {Nat.is_lt(Nat.add(1n+bp, 1n+bp), z) == True{} : Bool}, Nat.add(C.shift(63n, one), C.shift(63n, one)), C.shift(64n, one), Equal.sym(Nat, C.shift(64n, one), Nat.add(C.shift(63n, one), C.shift(63n, one)), NA.double_self(C.shift(63n, one))), h)

def fit_lt(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, C.shift(64n, one)) == True{} : Bool}) -> {C.fits(64n, x) == True{} : Bool}:
  WW.fits_one(64n, one, h1, x, h)

# the word r' of redc_p
def rp_val(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})) == Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))) : Nat}:
  +hr = rp_lt(one, h1, bp, tl, th, mp, pl, ph, T, eT, hT, eP, hinv, h63)
  +h64 = N.lt_trans(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Nat.add(1n+bp, 1n+bp), C.shift(64n, one), hr, mm64(one, bp, h63))
  +f1 = fit_lt(one, h1, Nat.add(SW.value(th), SW.value(ph)), N.le_lt_trans(Nat.add(SW.value(th), SW.value(ph)), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), C.shift(64n, one), N.le_add_right(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), h64))
  +e1 = M128.add64_exact(th, ph, f1)
  +e2 = Equal.trans(Nat, SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0}), v(X.b32(X.add_over(tl, pl))), S.bit_value(X.add_over(tl, pl)), M128.val0(X.b32(X.add_over(tl, pl))), b32v(X.add_over(tl, pl)))
  +es = Equal.trans(Nat, Nat.add(SW.value(X.add(th, ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), SW.value(X.add(th, ph)), Nat.add(SW.value(th), SW.value(ph)), e1), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(SW.value(th), SW.value(ph)), z), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0}), S.bit_value(X.add_over(tl, pl)), e2))
  +f2 = fit_lt(one, h1, Nat.add(SW.value(X.add(th, ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), L.subst(Nat, z => {Nat.is_lt(z, C.shift(64n, one)) == True{} : Bool}, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), Nat.add(SW.value(X.add(th, ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), Equal.sym(Nat, Nat.add(SW.value(X.add(th, ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), es), h64))
  Equal.trans(Nat, SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(SW.value(X.add(th, ph)), SW.value(WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), M128.add64_exact(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0}, f2), es)

# redc_p is r' mod m
def rp_mod(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {SW.value(X.redc_p(m, tl, th, (pl, ph))) == Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp) : Nat}:
  +ev = rp_val(one, h1, bp, m, mp, hM, hinv, h63, tl, th, pl, ph, T, eT, hT, eP)
  +hr = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(1n+bp, 1n+bp)) == True{} : Bool}, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})), Equal.sym(Nat, SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), ev), rp_lt(one, h1, bp, tl, th, mp, pl, ph, T, eT, hT, eP, hinv, h63))
  Equal.trans(Nat, SW.value(X.redc_p(m, tl, th, (pl, ph))), Nat.mod(SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})), 1n+bp), Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp), sif(bp, m, X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0}), hM, hr), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), SW.value(X.add(X.add(th, ph), WU.U64{X.b32(X.add_over(tl, pl)), 0})), Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), ev))

# redc_p is below m and is t / 2^64 (mod m)
def rp_lt_m(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {Nat.is_lt(SW.value(X.redc_p(m, tl, th, (pl, ph))), 1n+bp) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp), SW.value(X.redc_p(m, tl, th, (pl, ph))), Equal.sym(Nat, SW.value(X.redc_p(m, tl, th, (pl, ph))), Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp), rp_mod(one, h1, bp, m, mp, hM, hinv, h63, tl, th, pl, ph, T, eT, hT, eP)), NR.dm_lt(bp, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))))

def rp_cong(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, +pl: WU.U64, +ph: WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {Nat.mod(C.shift(64n, SW.value(X.redc_p(m, tl, th, (pl, ph)))), 1n+bp) == Nat.mod(T, 1n+bp) : Nat}:
  Equal.trans(Nat, Nat.mod(C.shift(64n, SW.value(X.redc_p(m, tl, th, (pl, ph)))), 1n+bp), Nat.mod(C.shift(64n, Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp)), 1n+bp), Nat.mod(T, 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(C.shift(64n, z), 1n+bp), SW.value(X.redc_p(m, tl, th, (pl, ph))), Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp), rp_mod(one, h1, bp, m, mp, hM, hinv, h63, tl, th, pl, ph, T, eT, hT, eP)), Equal.trans(Nat, Nat.mod(C.shift(64n, Nat.mod(Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl))), 1n+bp)), 1n+bp), Nat.mod(C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), 1n+bp), Nat.mod(T, 1n+bp), MN.mod_shift(bp, 64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), Equal.trans(Nat, Nat.mod(C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), 1n+bp), Nat.mod(Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), 1n+bp), Nat.mod(T, 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), C.shift(64n, Nat.add(Nat.add(SW.value(th), SW.value(ph)), S.bit_value(X.add_over(tl, pl)))), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), rp_eq(one, bp, tl, th, mp, pl, ph, T, eT, eP, hinv)), Equal.trans(Nat, Nat.mod(Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), 1n+bp), Nat.mod(Nat.add(Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp), T), 1n+bp), Nat.mod(T, 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.add(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp)), Nat.add(Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp), T), NA.add_comm(T, Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp))), NR.absorb(bp, SW.value(X.mul(tl, mp)), T)))))


def rpp_lt(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, p: WU.U64 & WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(X.pfst(p)), C.shift(64n, SW.value(X.psnd(p)))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {Nat.is_lt(SW.value(X.redc_p(m, tl, th, p)), 1n+bp) == True{} : Bool}:
  match p:
    case Tuple{+pl, +ph}:
      rp_lt_m(one, h1, bp, m, mp, hM, hinv, h63, tl, th, pl, ph, T, eT, hT, eP)

def rpp_cong(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +tl: WU.U64, +th: WU.U64, p: WU.U64 & WU.U64, +T: Nat, +eT: {Nat.add(SW.value(tl), C.shift(64n, SW.value(th))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}, +eP: {Nat.add(SW.value(X.pfst(p)), C.shift(64n, SW.value(X.psnd(p)))) == Nat.mul(SW.value(X.mul(tl, mp)), 1n+bp) : Nat}) -> {Nat.mod(C.shift(64n, SW.value(X.redc_p(m, tl, th, p))), 1n+bp) == Nat.mod(T, 1n+bp) : Nat}:
  match p:
    case Tuple{+pl, +ph}:
      rp_cong(one, h1, bp, m, mp, hM, hinv, h63, tl, th, pl, ph, T, eT, hT, eP)

def ep_m(+bp: Nat, +m: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +u: WU.U64) -> {Nat.add(SW.value(X.pfst(X.mul128(u, m))), C.shift(64n, SW.value(X.psnd(X.mul128(u, m))))) == Nat.mul(SW.value(u), 1n+bp) : Nat}:
  Equal.trans(Nat, Nat.add(SW.value(X.pfst(X.mul128(u, m))), C.shift(64n, SW.value(X.psnd(X.mul128(u, m))))), Nat.mul(SW.value(u), SW.value(m)), Nat.mul(SW.value(u), 1n+bp), m128v(u, m), Equal.cong(Nat, Nat, z => Nat.mul(SW.value(u), z), SW.value(m), 1n+bp, hM))

def rd_lt(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, t: WU.U64 & WU.U64, +T: Nat, +eT: {Nat.add(SW.value(X.pfst(t)), C.shift(64n, SW.value(X.psnd(t)))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}) -> {Nat.is_lt(SW.value(X.redc(m, mp, t)), 1n+bp) == True{} : Bool}:
  match t:
    case Tuple{+tl, +th}:
      rpp_lt(one, h1, bp, m, mp, hM, hinv, h63, tl, th, X.mul128(X.mul(tl, mp), m), T, eT, hT, ep_m(bp, m, hM, X.mul(tl, mp)))

def rd_cong(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, t: WU.U64 & WU.U64, +T: Nat, +eT: {Nat.add(SW.value(X.pfst(t)), C.shift(64n, SW.value(X.psnd(t)))) == T : Nat}, +hT: {Nat.is_lt(T, Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}) -> {Nat.mod(C.shift(64n, SW.value(X.redc(m, mp, t))), 1n+bp) == Nat.mod(T, 1n+bp) : Nat}:
  match t:
    case Tuple{+tl, +th}:
      rpp_cong(one, h1, bp, m, mp, hM, hinv, h63, tl, th, X.mul128(X.mul(tl, mp), m), T, eT, hT, ep_m(bp, m, hM, X.mul(tl, mp)))

def ab_lt(+bp: Nat, +a: Nat, +b: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +hb: {Nat.is_lt(b, 1n+bp) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, b), Nat.mul(1n+bp, 1n+bp)) == True{} : Bool}:
  N.le_lt_trans(Nat.mul(a, b), Nat.mul(a, 1n+bp), Nat.mul(1n+bp, 1n+bp), AQ.mle2(a, a, b, 1n+bp, N.le_refl(a), N.lt_le(b, 1n+bp, hb)), L.subst(Nat, z => {Nat.is_lt(Nat.mul(a, 1n+bp), z) == True{} : Bool}, Nat.mul(1n+bp, 1n+bp), Nat.mul(1n+bp, 1n+bp), {==}, lt_mul(a, 1n+bp, 1n+bp, ha, {==})))

# Montgomery multiplication: mont(a, b) < m and mont(a, b) 2^64 == a b (mod m)
def mont_lt(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +a: WU.U64, +b: WU.U64, +ha: {Nat.is_lt(SW.value(a), 1n+bp) == True{} : Bool}, +hb: {Nat.is_lt(SW.value(b), 1n+bp) == True{} : Bool}) -> {Nat.is_lt(SW.value(X.mont(m, mp, a, b)), 1n+bp) == True{} : Bool}:
  rd_lt(one, h1, bp, m, mp, hM, hinv, h63, X.mul128(a, b), Nat.mul(SW.value(a), SW.value(b)), m128v(a, b), ab_lt(bp, SW.value(a), SW.value(b), ha, hb))

def mont_cong(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +a: WU.U64, +b: WU.U64, +ha: {Nat.is_lt(SW.value(a), 1n+bp) == True{} : Bool}, +hb: {Nat.is_lt(SW.value(b), 1n+bp) == True{} : Bool}) -> {Nat.mod(C.shift(64n, SW.value(X.mont(m, mp, a, b))), 1n+bp) == Nat.mod(Nat.mul(SW.value(a), SW.value(b)), 1n+bp) : Nat}:
  rd_cong(one, h1, bp, m, mp, hM, hinv, h63, X.mul128(a, b), Nat.mul(SW.value(a), SW.value(b)), m128v(a, b), ab_lt(bp, SW.value(a), SW.value(b), ha, hb))


def mlt(+bp: Nat, +x: Nat) -> {Nat.is_lt(Nat.mod(x, 1n+bp), 1n+bp) == True{} : Bool}:
  NR.dm_lt(bp, x)

def smul(+x: Nat, +y: Nat) -> {Nat.mul(C.shift(64n, x), C.shift(64n, y)) == C.shift(64n, C.shift(64n, Nat.mul(x, y))) : Nat}:
  Equal.trans(Nat, Nat.mul(C.shift(64n, x), C.shift(64n, y)), C.shift(64n, Nat.mul(x, C.shift(64n, y))), C.shift(64n, C.shift(64n, Nat.mul(x, y))), WW.shift_mul_l(64n, x, C.shift(64n, y)), Equal.cong(Nat, Nat, z => C.shift(64n, z), Nat.mul(x, C.shift(64n, y)), C.shift(64n, Nat.mul(x, y)), WW.shift_mul_r(64n, x, y)))

# on Montgomery forms: mont(a R, b R) == (a b mod m) R (mod m)
def mform(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +hh: Nat, +hH: {1n+1n+bp == Nat.add(hh, hh) : Nat}, +a: WU.U64, +b: WU.U64, +an: Nat, +bn: Nat, +ha: {SW.value(a) == Nat.mod(C.shift(64n, an), 1n+bp) : Nat}, +hb: {SW.value(b) == Nat.mod(C.shift(64n, bn), 1n+bp) : Nat}) -> {SW.value(X.mont(m, mp, a, b)) == Nat.mod(C.shift(64n, Nat.mod(Nat.mul(an, bn), 1n+bp)), 1n+bp) : Nat}:
  +la = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(C.shift(64n, an), 1n+bp), SW.value(a), Equal.sym(Nat, SW.value(a), Nat.mod(C.shift(64n, an), 1n+bp), ha), mlt(bp, C.shift(64n, an)))
  +lb = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(C.shift(64n, bn), 1n+bp), SW.value(b), Equal.sym(Nat, SW.value(b), Nat.mod(C.shift(64n, bn), 1n+bp), hb), mlt(bp, C.shift(64n, bn)))
  +o = SW.value(X.mont(m, mp, a, b))
  +e1 = Equal.trans(Nat, Nat.mod(C.shift(64n, o), 1n+bp), Nat.mod(Nat.mul(SW.value(a), SW.value(b)), 1n+bp), Nat.mod(C.shift(64n, C.shift(64n, Nat.mul(an, bn))), 1n+bp), mont_cong(one, h1, bp, m, mp, hM, hinv, h63, a, b, la, lb), Equal.trans(Nat, Nat.mod(Nat.mul(SW.value(a), SW.value(b)), 1n+bp), Nat.mod(Nat.mul(Nat.mod(C.shift(64n, an), 1n+bp), SW.value(b)), 1n+bp), Nat.mod(C.shift(64n, C.shift(64n, Nat.mul(an, bn))), 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(z, SW.value(b)), 1n+bp), SW.value(a), Nat.mod(C.shift(64n, an), 1n+bp), ha), Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(C.shift(64n, an), 1n+bp), SW.value(b)), 1n+bp), Nat.mod(Nat.mul(Nat.mod(C.shift(64n, an), 1n+bp), Nat.mod(C.shift(64n, bn), 1n+bp)), 1n+bp), Nat.mod(C.shift(64n, C.shift(64n, Nat.mul(an, bn))), 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(Nat.mod(C.shift(64n, an), 1n+bp), z), 1n+bp), SW.value(b), Nat.mod(C.shift(64n, bn), 1n+bp), hb), Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(C.shift(64n, an), 1n+bp), Nat.mod(C.shift(64n, bn), 1n+bp)), 1n+bp), Nat.mod(Nat.mul(C.shift(64n, an), Nat.mod(C.shift(64n, bn), 1n+bp)), 1n+bp), Nat.mod(C.shift(64n, C.shift(64n, Nat.mul(an, bn))), 1n+bp), NR.mod_mul_l(bp, C.shift(64n, an), Nat.mod(C.shift(64n, bn), 1n+bp)), Equal.trans(Nat, Nat.mod(Nat.mul(C.shift(64n, an), Nat.mod(C.shift(64n, bn), 1n+bp)), 1n+bp), Nat.mod(Nat.mul(C.shift(64n, an), C.shift(64n, bn)), 1n+bp), Nat.mod(C.shift(64n, C.shift(64n, Nat.mul(an, bn))), 1n+bp), NR.mod_mul_r(bp, C.shift(64n, an), C.shift(64n, bn)), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.mul(C.shift(64n, an), C.shift(64n, bn)), C.shift(64n, C.shift(64n, Nat.mul(an, bn))), smul(an, bn)))))))
  +e2 = MN.cancel(bp, hh, hH, 64n, o, C.shift(64n, Nat.mul(an, bn)), e1)
  +lo = mont_lt(one, h1, bp, m, mp, hM, hinv, h63, a, b, la, lb)
  +e3 = Equal.sym(Nat, Nat.mod(o, 1n+bp), o, NR.mod_of(0n, bp, o, lo))
  Equal.trans(Nat, o, Nat.mod(o, 1n+bp), Nat.mod(C.shift(64n, Nat.mod(Nat.mul(an, bn), 1n+bp)), 1n+bp), e3, Equal.trans(Nat, Nat.mod(o, 1n+bp), Nat.mod(C.shift(64n, Nat.mul(an, bn)), 1n+bp), Nat.mod(C.shift(64n, Nat.mod(Nat.mul(an, bn), 1n+bp)), 1n+bp), e2, Equal.sym(Nat, Nat.mod(C.shift(64n, Nat.mod(Nat.mul(an, bn), 1n+bp)), 1n+bp), Nat.mod(C.shift(64n, Nat.mul(an, bn)), 1n+bp), MN.mod_shift(bp, 64n, Nat.mul(an, bn)))))

def mbit_v(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +hh: Nat, +hH: {1n+1n+bp == Nat.add(hh, hh) : Nat}, +b: WU.U64, +acc: WU.U64, +bn: Nat, +an: Nat, +hb: {SW.value(b) == Nat.mod(C.shift(64n, bn), 1n+bp) : Nat}, +ha: {SW.value(acc) == Nat.mod(C.shift(64n, an), 1n+bp) : Nat}, +d: Nat, +o: Bool, +hd: {Nat.is_lt(d, 2n) == True{} : Bool}, +ho: {o == Nat.is_eq(d, 1n) : Bool}) -> {SW.value(X.mbit(o, m, mp, b, acc)) == Nat.mod(C.shift(64n, M.pow_mod_odd(1n+bp, d, bn, an)), 1n+bp) : Nat}:
  match d o:
    case 0n False{}:
      ha
    case 0n True{}:
      Empty.absurd({SW.value(X.mbit(True{}, m, mp, b, acc)) == Nat.mod(C.shift(64n, M.pow_mod_odd(1n+bp, 0n, bn, an)), 1n+bp) : Nat}, true_ne_false(ho))
    case 1n True{}:
      mform(one, h1, bp, m, mp, hM, hinv, h63, hh, hH, acc, b, an, bn, ha, hb)
    case 1n False{}:
      Empty.absurd({SW.value(X.mbit(False{}, m, mp, b, acc)) == Nat.mod(C.shift(64n, M.pow_mod_odd(1n+bp, 1n, bn, an)), 1n+bp) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, ho)))
    case 2n+q _:
      Empty.absurd({SW.value(X.mbit(o, m, mp, b, acc)) == Nat.mod(C.shift(64n, M.pow_mod_odd(1n+bp, 2n+q, bn, an)), 1n+bp) : Nat}, N.lt_zero_absurd(q, hd))

def izv(+a: WU.U64, +n: Nat, +h: {SW.value(a) == n : Nat}) -> {X.is_zero(a) == Nat.is_eq(n, 0n) : Bool}:
  Equal.trans(Bool, X.is_zero(a), Nat.is_eq(SW.value(a), 0n), Nat.is_eq(n, 0n), WA.is_zero_value(a), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), SW.value(a), n, h))

# the Montgomery loop computes pow_mod_go on the forms
def msim(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +mp: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +hh: Nat, +hH: {1n+1n+bp == Nat.add(hh, hh) : Nat}, +f: Nat, +b: WU.U64, +acc: WU.U64, +e: WU.U64, +bn: Nat, +an: Nat, +hb: {SW.value(b) == Nat.mod(C.shift(64n, bn), 1n+bp) : Nat}, +ha: {SW.value(acc) == Nat.mod(C.shift(64n, an), 1n+bp) : Nat}, +ez: Bool, +ne: Nat, +hez: {X.is_zero(e) == ez : Bool}, +hne: {SW.value(e) == ne : Nat}) -> {SW.value(X.mpow_go(f, m, mp, b, acc, (e, ez))) == Nat.mod(C.shift(64n, M.pow_mod_go(f, 1n+bp, ne, bn, an)), 1n+bp) : Nat}:
  match f ez ne:
    case 0n _ _:
      ha
    case 1n+g True{} 0n:
      ha
    case 1n+g True{} 1n+ep:
      Empty.absurd({SW.value(X.mpow_go(1n+g, m, mp, b, acc, (e, True{}))) == Nat.mod(C.shift(64n, M.pow_mod_go(1n+g, 1n+bp, 1n+ep, bn, an)), 1n+bp) : Nat}, true_ne_false(Equal.trans(Bool, True{}, X.is_zero(e), False{}, Equal.sym(Bool, X.is_zero(e), True{}, hez), izv(e, 1n+ep, hne))))
    case 1n+g False{} 0n:
      Empty.absurd({SW.value(X.mpow_go(1n+g, m, mp, b, acc, (e, False{}))) == Nat.mod(C.shift(64n, M.pow_mod_go(1n+g, 1n+bp, 0n, bn, an)), 1n+bp) : Nat}, true_ne_false(Equal.trans(Bool, True{}, X.is_zero(e), False{}, Equal.sym(Bool, X.is_zero(e), True{}, izv(e, 0n, hne)), hez)))
    case 1n+ +g False{} 1n+ +ep:
      +b2 = X.mont(m, mp, b, b)
      +eb2 = mform(one, h1, bp, m, mp, hM, hinv, h63, hh, hH, b, b, bn, bn, hb, hb)
      +o = X.odd(e)
      +d = Nat.mod(1n+ep, 2n)
      +ho = Equal.trans(Bool, o, Nat.is_eq(Nat.mod(SW.value(e), 2n), 1n), Nat.is_eq(d, 1n), WA.odd_value(e), Equal.cong(Nat, Bool, t => Nat.is_eq(Nat.mod(t, 2n), 1n), SW.value(e), 1n+ep, hne))
      +a2 = X.mbit(o, m, mp, b, acc)
      +ea2 = mbit_v(one, h1, bp, m, mp, hM, hinv, h63, hh, hH, b, acc, bn, an, hb, ha, d, o, NR.dm_lt(1n, 1n+ep), ho)
      +e2 = X.half(e)
      +ee2 = Equal.trans(Nat, SW.value(e2), Nat.div(SW.value(e), 2n), Nat.div(1n+ep, 2n), WA.half_value(e), Equal.cong(Nat, Nat, t => Nat.div(t, 2n), SW.value(e), 1n+ep, hne))
      msim(one, h1, bp, m, mp, hM, hinv, h63, hh, hH, g, b2, a2, e2, Nat.mod(Nat.mul(bn, bn), 1n+bp), M.pow_mod_odd(1n+bp, d, bn, an), eb2, ea2, X.is_zero(e2), Nat.div(1n+ep, 2n), {==}, ee2)


def not_t(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

# x 2^64 mod m by two 2^32 reductions
def to_mont_v(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +hz: {U32.is_zero(mh) == False{} : Bool}, +x: WU.U64, +hx: {Nat.is_lt(SW.value(x), 1n+bp) == True{} : Bool}) -> {SW.value(X.to_mont(x, WU.U64{ml, mh})) == Nat.mod(C.shift(64n, SW.value(x)), 1n+bp) : Nat}:
  +r1 = X.red96(x, 0, WU.U64{ml, mh})
  +hx1 = L.subst(Nat, z => {Nat.is_lt(SW.value(x), z) == True{} : Bool}, 1n+bp, SW.value(WU.U64{ml, mh}), Equal.sym(Nat, SW.value(WU.U64{ml, mh}), 1n+bp, hM), hx)
  +e1 = Equal.trans(Nat, SW.value(r1), Nat.mod(Nat.add(v(0), C.shift(32n, SW.value(x))), SW.value(WU.U64{ml, mh})), Nat.mod(C.shift(32n, SW.value(x)), 1n+bp), MM.red_vg(one, h1, 0, x, ml, mh, hx1, hz), Equal.cong(Nat, Nat, z => Nat.mod(C.shift(32n, SW.value(x)), z), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
  +l1 = L.subst(Nat, z => {Nat.is_lt(z, SW.value(WU.U64{ml, mh})) == True{} : Bool}, Nat.mod(C.shift(32n, SW.value(x)), 1n+bp), SW.value(r1), Equal.sym(Nat, SW.value(r1), Nat.mod(C.shift(32n, SW.value(x)), 1n+bp), e1), L.subst(Nat, z => {Nat.is_lt(Nat.mod(C.shift(32n, SW.value(x)), 1n+bp), z) == True{} : Bool}, 1n+bp, SW.value(WU.U64{ml, mh}), Equal.sym(Nat, SW.value(WU.U64{ml, mh}), 1n+bp, hM), mlt(bp, C.shift(32n, SW.value(x)))))
  +e2 = Equal.trans(Nat, SW.value(X.red96(r1, 0, WU.U64{ml, mh})), Nat.mod(Nat.add(v(0), C.shift(32n, SW.value(r1))), SW.value(WU.U64{ml, mh})), Nat.mod(C.shift(32n, SW.value(r1)), 1n+bp), MM.red_vg(one, h1, 0, r1, ml, mh, l1, hz), Equal.cong(Nat, Nat, z => Nat.mod(C.shift(32n, SW.value(r1)), z), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
  Equal.trans(Nat, SW.value(X.red96(r1, 0, WU.U64{ml, mh})), Nat.mod(C.shift(32n, SW.value(r1)), 1n+bp), Nat.mod(C.shift(64n, SW.value(x)), 1n+bp), e2, Equal.trans(Nat, Nat.mod(C.shift(32n, SW.value(r1)), 1n+bp), Nat.mod(C.shift(32n, Nat.mod(C.shift(32n, SW.value(x)), 1n+bp)), 1n+bp), Nat.mod(C.shift(64n, SW.value(x)), 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(C.shift(32n, z), 1n+bp), SW.value(r1), Nat.mod(C.shift(32n, SW.value(x)), 1n+bp), e1), Equal.trans(Nat, Nat.mod(C.shift(32n, Nat.mod(C.shift(32n, SW.value(x)), 1n+bp)), 1n+bp), Nat.mod(C.shift(32n, C.shift(32n, SW.value(x))), 1n+bp), Nat.mod(C.shift(64n, SW.value(x)), 1n+bp), MN.mod_shift(bp, 32n, C.shift(32n, SW.value(x))), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), C.shift(32n, C.shift(32n, SW.value(x))), C.shift(64n, SW.value(x)), Equal.sym(Nat, C.shift(64n, SW.value(x)), C.shift(32n, C.shift(32n, SW.value(x))), WW.shift_comp(32n, 32n, SW.value(x)))))))

def pmo_lt(+bp: Nat, +d: Nat, +base: Nat, +acc: Nat, +ha: {Nat.is_lt(acc, 1n+bp) == True{} : Bool}) -> {Nat.is_lt(M.pow_mod_odd(1n+bp, d, base, acc), 1n+bp) == True{} : Bool}:
  match d:
    case 0n:
      ha
    case 1n+z:
      NR.dm_lt(bp, Nat.mul(acc, base))

def pm_lt(+bp: Nat, +f: Nat, +e: Nat, +base: Nat, +acc: Nat, +ha: {Nat.is_lt(acc, 1n+bp) == True{} : Bool}) -> {Nat.is_lt(M.pow_mod_go(f, 1n+bp, e, base, acc), 1n+bp) == True{} : Bool}:
  match f e:
    case 0n _:
      ha
    case 1n+g 0n:
      ha
    case 1n+ +g 1n+ +ep:
      pm_lt(bp, g, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(base, base), 1n+bp), M.pow_mod_odd(1n+bp, Nat.mod(1n+ep, 2n), base, acc), pmo_lt(bp, Nat.mod(1n+ep, 2n), base, acc, ha))

# 2 <= m for a nonzero high word
# 2 <= lo + 2^(1+k) h for h > 0, over an open width (k is 31 at the use):
# a closed 2^32 in a goal is expanded by the checker
def two_le_k(+k: Nat, +lo: Nat, +h: Nat, +hh: {Nat.is_eq(h, 0n) == False{} : Bool}) -> {Nat.is_le(2n, Nat.add(lo, C.shift(1n+k, h))) == True{} : Bool}:
  +a1 = WW.shift_mono(1n+k, 1n, h, WA.pos_ne(h, hh))
  +s1 = C.shift(k, 1n)
  +a2 = SQ2.le_add2(1n, s1, 1n, s1, WW.shift_ge(k, 1n), WW.shift_ge(k, 1n))
  +a3 = L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, Nat.add(s1, s1), C.shift(1n+k, 1n), Equal.sym(Nat, C.shift(1n+k, 1n), Nat.add(s1, s1), NA.double_self(s1)), a2)
  +a4 = N.le_trans(2n, C.shift(1n+k, 1n), C.shift(1n+k, h), a3, a1)
  N.le_trans(2n, C.shift(1n+k, h), Nat.add(lo, C.shift(1n+k, h)), a4, L.subst(Nat, z => {Nat.is_le(C.shift(1n+k, h), z) == True{} : Bool}, Nat.add(C.shift(1n+k, h), lo), Nat.add(lo, C.shift(1n+k, h)), NA.add_comm(C.shift(1n+k, h), lo), N.le_add_right(C.shift(1n+k, h), lo)))

def two_le(+ml: U32, +mh: U32, +hz: {U32.is_zero(mh) == False{} : Bool}) -> {Nat.is_le(2n, SW.value(WU.U64{ml, mh})) == True{} : Bool}:
  two_le_k(31n, v(ml), v(mh), Equal.trans(Bool, Nat.is_eq(v(mh), 0n), U32.is_zero(mh), False{}, Equal.sym(Bool, U32.is_zero(mh), Nat.is_eq(v(mh), 0n), LW.zero_nat(mh)), hz))


# the Montgomery pow_mod is pow_mod_go on the values
def mpow_v(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +mp: WU.U64, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +hodd: {Nat.mod(1n+bp, 2n) == 1n : Nat}, +hinv: {1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))) == C.shift(64n, one) : Nat}, +h63: {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}, +hz: {U32.is_zero(mh) == False{} : Bool}, +b: WU.U64, +hb: {Nat.is_lt(SW.value(b), 1n+bp) == True{} : Bool}, +e: WU.U64) -> {SW.value(X.mpow_m(b, e, WU.U64{ml, mh}, mp)) == M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)) : Nat}:
  +hh : Nat = 1n+Nat.div(1n+bp, 2n)
  +hH = MN.odd_hh(bp, hodd)
  +bt = X.to_mont(b, WU.U64{ml, mh})
  +eb = to_mont_v(one, h1, bp, ml, mh, hM, hz, b, hb)
  +hnz = Equal.trans(Bool, X.is_zero(WU.U64{ml, mh}), Nat.is_eq(SW.value(WU.U64{ml, mh}), 0n), False{}, WA.is_zero_value(WU.U64{ml, mh}), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
  +o1 = X.rem(WU.U64{1, 0}, WU.U64{ml, mh})
  +eo = Equal.trans(Nat, SW.value(o1), Nat.mod(SW.value(WU.U64{1, 0}), SW.value(WU.U64{ml, mh})), Nat.mod(1n, 1n+bp), DR.divmod_rem(WU.U64{1, 0}, WU.U64{ml, mh}, hnz), Equal.cong(Nat, Nat, z => Nat.mod(1n, z), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
  +lo1 = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(1n, 1n+bp), SW.value(o1), Equal.sym(Nat, SW.value(o1), Nat.mod(1n, 1n+bp), eo), mlt(bp, 1n))
  +at = X.to_mont(o1, WU.U64{ml, mh})
  +ea = Equal.trans(Nat, SW.value(at), Nat.mod(C.shift(64n, SW.value(o1)), 1n+bp), Nat.mod(C.shift(64n, Nat.mod(1n, 1n+bp)), 1n+bp), to_mont_v(one, h1, bp, ml, mh, hM, hz, o1, lo1), Equal.cong(Nat, Nat, z => Nat.mod(C.shift(64n, z), 1n+bp), SW.value(o1), Nat.mod(1n, 1n+bp), eo))
  +go = X.mpow_go(140n, WU.U64{ml, mh}, mp, bt, at, (e, X.is_zero(e)))
  +eg = msim(one, h1, bp, WU.U64{ml, mh}, mp, hM, hinv, h63, hh, hH, 140n, bt, at, e, SW.value(b), Nat.mod(1n, 1n+bp), eb, ea, X.is_zero(e), SW.value(e), {==}, {==})
  +lg = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), SW.value(go), Equal.sym(Nat, SW.value(go), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), eg), mlt(bp, C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)))))
  +l1 = N.lt_le_trans(1n, 2n, 1n+bp, {==}, L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, SW.value(WU.U64{ml, mh}), 1n+bp, hM, two_le(ml, mh, hz)))
  +o = SW.value(X.mont(WU.U64{ml, mh}, mp, go, WU.U64{1, 0}))
  +c1 = Equal.trans(Nat, Nat.mod(C.shift(64n, o), 1n+bp), Nat.mod(Nat.mul(SW.value(go), SW.value(WU.U64{1, 0})), 1n+bp), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), mont_cong(one, h1, bp, WU.U64{ml, mh}, mp, hM, hinv, h63, go, WU.U64{1, 0}, lg, l1), Equal.trans(Nat, Nat.mod(Nat.mul(SW.value(go), SW.value(WU.U64{1, 0})), 1n+bp), Nat.mod(Nat.mul(SW.value(go), 1n), 1n+bp), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), {==}, Equal.trans(Nat, Nat.mod(Nat.mul(SW.value(go), 1n), 1n+bp), Nat.mod(SW.value(go), 1n+bp), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.mul(SW.value(go), 1n), SW.value(go), NA.mul_one(SW.value(go))), Equal.trans(Nat, Nat.mod(SW.value(go), 1n+bp), Nat.mod(Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), 1n+bp), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), SW.value(go), Nat.mod(C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))), 1n+bp), eg), NR.mod_mod(bp, C.shift(64n, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp))))))))
  +c2 = MN.cancel(bp, hh, hH, 64n, o, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)), c1)
  +lo = mont_lt(one, h1, bp, WU.U64{ml, mh}, mp, hM, hinv, h63, go, WU.U64{1, 0}, lg, l1)
  +hP = pm_lt(bp, 140n, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp), mlt(bp, 1n))
  +z1 = Equal.sym(Nat, Nat.mod(o, 1n+bp), o, NR.mod_of(0n, bp, o, lo))
  +z2 = NR.mod_of(0n, bp, M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)), hP)
  +z3 = Equal.trans(Nat, Nat.mod(o, 1n+bp), Nat.mod(M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)), 1n+bp), M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)), c2, z2)
  +z4 = Equal.trans(Nat, o, Nat.mod(o, 1n+bp), M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(b), Nat.mod(1n, 1n+bp)), z1, z3)
  z4


# what mont_ok(m) gives
def mok_ab(+ml: U32, +mh: U32, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {Bool.and(X.odd(WU.U64{ml, mh}), X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{4294967295, 4294967295})) == True{} : Bool}:
  W64S.and_l(Bool.and(X.odd(WU.U64{ml, mh}), X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{4294967295, 4294967295})), Bool.and(Bool.not(U32.is_zero(mh)), U32.is_lt(mh, 2147483648)), hok)

def mok_cd(+ml: U32, +mh: U32, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {Bool.and(Bool.not(U32.is_zero(mh)), U32.is_lt(mh, 2147483648)) == True{} : Bool}:
  W64S.and_r(Bool.and(X.odd(WU.U64{ml, mh}), X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{4294967295, 4294967295})), Bool.and(Bool.not(U32.is_zero(mh)), U32.is_lt(mh, 2147483648)), hok)

def mok_odd(+bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {Nat.mod(1n+bp, 2n) == 1n : Nat}:
  +h = Equal.trans(Bool, Nat.is_eq(Nat.mod(SW.value(WU.U64{ml, mh}), 2n), 1n), X.odd(WU.U64{ml, mh}), True{}, Equal.sym(Bool, X.odd(WU.U64{ml, mh}), Nat.is_eq(Nat.mod(SW.value(WU.U64{ml, mh}), 2n), 1n), WA.odd_value(WU.U64{ml, mh})), W64S.and_l(X.odd(WU.U64{ml, mh}), X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{4294967295, 4294967295}), mok_ab(ml, mh, hok)))
  Equal.trans(Nat, Nat.mod(1n+bp, 2n), Nat.mod(SW.value(WU.U64{ml, mh}), 2n), 1n, Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), 1n+bp, SW.value(WU.U64{ml, mh}), Equal.sym(Nat, SW.value(WU.U64{ml, mh}), 1n+bp, hM)), N.eq_from_is_eq(Nat.mod(SW.value(WU.U64{ml, mh}), 2n), 1n, h))

# over an open all-ones word o: a literal 2^64 - 1 under SW.value would be
# expanded in unary by any conversion that unfolds it
def mok_inv_o(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +o: U32, +po: {o == U32{WD.mask(32n, 32n)} : U32}, +heq: {X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{o, o}) == True{} : Bool}) -> {1n+C.low(64n, Nat.mul(1n+bp, SW.value(X.minv(WU.U64{ml, mh})))) == C.shift(64n, one) : Nat}:
  +mp = X.minv(WU.U64{ml, mh})
  +w = X.mul(WU.U64{ml, mh}, mp)
  +h = Equal.trans(Bool, Nat.is_eq(SW.value(w), SW.value(WU.U64{o, o})), X.eq(w, WU.U64{o, o}), True{}, Equal.sym(Bool, X.eq(w, WU.U64{o, o}), Nat.is_eq(SW.value(w), SW.value(WU.U64{o, o})), WA.eq_value(w, WU.U64{o, o})), heq)
  +e1 = N.eq_from_is_eq(SW.value(w), SW.value(WU.U64{o, o}), h)
  +e2 = Equal.trans(Nat, C.low(64n, Nat.mul(1n+bp, SW.value(mp))), C.low(64n, Nat.mul(SW.value(WU.U64{ml, mh}), SW.value(mp))), SW.value(w), Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(z, SW.value(mp))), 1n+bp, SW.value(WU.U64{ml, mh}), Equal.sym(Nat, SW.value(WU.U64{ml, mh}), 1n+bp, hM)), Equal.sym(Nat, SW.value(w), C.low(64n, Nat.mul(SW.value(WU.U64{ml, mh}), SW.value(mp))), WA.mul_value(WU.U64{ml, mh}, mp)))
  Equal.trans(Nat, 1n+C.low(64n, Nat.mul(1n+bp, SW.value(mp))), 1n+SW.value(WU.U64{o, o}), C.shift(64n, one), Equal.cong(Nat, Nat, z => 1n+z, C.low(64n, Nat.mul(1n+bp, SW.value(mp))), SW.value(WU.U64{o, o}), Equal.trans(Nat, C.low(64n, Nat.mul(1n+bp, SW.value(mp))), SW.value(w), SW.value(WU.U64{o, o}), e2, e1)), ones_v(one, h1, o, po))

def mok_inv(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {1n+C.low(64n, Nat.mul(1n+bp, SW.value(X.minv(WU.U64{ml, mh})))) == C.shift(64n, one) : Nat}:
  mok_inv_o(one, h1, bp, ml, mh, hM, 4294967295, {==}, W64S.and_r(X.odd(WU.U64{ml, mh}), X.eq(X.mul(WU.U64{ml, mh}, X.minv(WU.U64{ml, mh})), WU.U64{4294967295, 4294967295}), mok_ab(ml, mh, hok)))

def mok_hz(+ml: U32, +mh: U32, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {U32.is_zero(mh) == False{} : Bool}:
  not_t(U32.is_zero(mh), W64S.and_l(Bool.not(U32.is_zero(mh)), U32.is_lt(mh, 2147483648), mok_cd(ml, mh, hok)))

# over an open 2^31 word c: comparisons never meet the literal
def mok_63_c(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}, +hlt: {U32.is_lt(mh, c) == True{} : Bool}) -> {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}:
  +s31 = C.shift(31n, one)
  +e31 = Equal.trans(Nat, v(c), WD.sc(31n, one), s31, PD.pow32(31n, {==}, one, h1, c, hc), Equal.sym(Nat, s31, WD.sc(31n, one), W64M.shift_sc(31n, one)))
  +hd = Equal.trans(Bool, Nat.is_lt(v(mh), v(c)), U32.is_lt(mh, c), True{}, Equal.sym(Bool, U32.is_lt(mh, c), Nat.is_lt(v(mh), v(c)), U.is_lt_nat(mh, c)), hlt)
  +hd2 = L.subst(Nat, z => {Nat.is_lt(v(mh), z) == True{} : Bool}, v(c), s31, e31, hd)
  +a1 = N.lt_add_r2(v(ml), C.shift(32n, one), C.shift(32n, v(mh)), WW.lt_one(32n, one, h1, v(ml), LW.vb(ml)))
  +a2 = L.subst(Nat, z => {Nat.is_lt(SW.value(WU.U64{ml, mh}), z) == True{} : Bool}, Nat.add(C.shift(32n, one), C.shift(32n, v(mh))), C.shift(32n, Nat.add(one, v(mh))), Equal.sym(Nat, C.shift(32n, Nat.add(one, v(mh))), Nat.add(C.shift(32n, one), C.shift(32n, v(mh))), WW.shift_add(32n, one, v(mh))), a1)
  +a3 = WW.shift_mono(32n, Nat.add(one, v(mh)), s31, L.subst(Nat, z => {Nat.is_le(Nat.add(z, v(mh)), s31) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le_succ(v(mh), s31, hd2)))
  +a4 = L.subst(Nat, z => {Nat.is_le(C.shift(32n, Nat.add(one, v(mh))), z) == True{} : Bool}, C.shift(32n, s31), C.shift(63n, one), Equal.sym(Nat, C.shift(63n, one), C.shift(32n, s31), WW.shift_comp(32n, 31n, one)), a3)
  L.subst(Nat, z => {Nat.is_lt(z, C.shift(63n, one)) == True{} : Bool}, SW.value(WU.U64{ml, mh}), 1n+bp, hM, N.lt_le_trans(SW.value(WU.U64{ml, mh}), C.shift(32n, Nat.add(one, v(mh))), C.shift(63n, one), a2, a4))


def mok_63(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +ml: U32, +mh: U32, +hM: {SW.value(WU.U64{ml, mh}) == 1n+bp : Nat}, +hok: {X.mont_ok(WU.U64{ml, mh}) == True{} : Bool}) -> {Nat.is_lt(1n+bp, C.shift(63n, one)) == True{} : Bool}:
  mok_63_c(one, h1, bp, ml, mh, hM, 2147483648, {==}, W64S.and_r(Bool.not(U32.is_zero(mh)), U32.is_lt(mh, 2147483648), mok_cd(ml, mh, hok)))

# pow_mod through Montgomery multiplication when mont_ok(m)
def mpow_top(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +m: WU.U64, +hM: {SW.value(m) == 1n+bp : Nat}, +hok: {X.mont_ok(m) == True{} : Bool}, +b: WU.U64, +e: WU.U64) -> {SW.value(X.mpow(X.rem(b, m), e, m)) == M.pow_mod_go(140n, 1n+bp, SW.value(e), Nat.mod(SW.value(b), 1n+bp), Nat.mod(1n, 1n+bp)) : Nat}:
  match m:
    case WU.U64{+ml, +mh}:
      +hnz = Equal.trans(Bool, X.is_zero(WU.U64{ml, mh}), Nat.is_eq(SW.value(WU.U64{ml, mh}), 0n), False{}, WA.is_zero_value(WU.U64{ml, mh}), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
      +rb = X.rem(b, WU.U64{ml, mh})
      +erb = Equal.trans(Nat, SW.value(rb), Nat.mod(SW.value(b), SW.value(WU.U64{ml, mh})), Nat.mod(SW.value(b), 1n+bp), DR.divmod_rem(b, WU.U64{ml, mh}, hnz), Equal.cong(Nat, Nat, z => Nat.mod(SW.value(b), z), SW.value(WU.U64{ml, mh}), 1n+bp, hM))
      +hb = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(SW.value(b), 1n+bp), SW.value(rb), Equal.sym(Nat, SW.value(rb), Nat.mod(SW.value(b), 1n+bp), erb), mlt(bp, SW.value(b)))
      +ev = mpow_v(one, h1, bp, ml, mh, X.minv(WU.U64{ml, mh}), hM, mok_odd(bp, ml, mh, hM, hok), mok_inv(one, h1, bp, ml, mh, hM, hok), mok_63(one, h1, bp, ml, mh, hM, hok), mok_hz(ml, mh, hok), rb, hb, e)
      Equal.trans(Nat, SW.value(X.mpow(rb, e, WU.U64{ml, mh})), M.pow_mod_go(140n, 1n+bp, SW.value(e), SW.value(rb), Nat.mod(1n, 1n+bp)), M.pow_mod_go(140n, 1n+bp, SW.value(e), Nat.mod(SW.value(b), 1n+bp), Nat.mod(1n, 1n+bp)), ev, Equal.cong(Nat, Nat, z => M.pow_mod_go(140n, 1n+bp, SW.value(e), z, Nat.mod(1n, 1n+bp)), SW.value(rb), Nat.mod(SW.value(b), 1n+bp), erb))
