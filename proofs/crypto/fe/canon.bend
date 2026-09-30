import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./nl.bend as NL
import ./pw.bend as PW
import ./carry.bend as CA
import ./pass.bend as PS
import ./sub.bend as SB
import ./ops.bend as OP

# freeze (src/crypto/curve25519/limbs.bend freeze_l = csub . pass . pass):
# from limbs below 2^19, the first pass leaves limbs of at most R and a
# value below 2^255 + 95; the second leaves limbs below R (its carry out is
# 0 or 1, and when it is 1 the low limbs hold less than 95, so 19 more stays
# below R); then x + 19 carries out of 2^255 exactly when x >= p, and the
# selected limbs are x mod p (TweetNaCl's car25519 + pack25519 argument, in
# radix 2^17).

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- lengths ----

def carry_len(+R: Nat, +xs: List<&2, Nat>, +c: Nat) -> {PS.ln(LS.cr_limbs(LS.carry(R, xs, c))) == PS.ln(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      +r = LS.carry(R, t, Nat.div(s, R))
      +e = Equal.cong(List<&2, Nat>, Nat, z => PS.ln(z), LS.cr_limbs(LS.cr_con(Nat.mod(s, R), r)), Con{Nat.mod(s, R), LS.cr_limbs(r)}, CA.cl_con(Nat.mod(s, R), r))
      tr(PS.ln(LS.cr_limbs(LS.cr_con(Nat.mod(s, R), r))), 1n+PS.ln(LS.cr_limbs(r)), 1n+PS.ln(t), e, Equal.cong(Nat, Nat, z => 1n+z, PS.ln(LS.cr_limbs(r)), PS.ln(t), carry_len(R, t, Nat.div(s, R))))

# the pass of two or more limbs: its limbs
def pass_shape(+R: Nat, +x0: Nat, +x1: Nat, +rest: List<&2, Nat>) -> {LS.pass(R, Con{x0, Con{x1, rest}}) == LS.pass_fin(R, LS.Cr{Con{Nat.mod(x0, R), Con{Nat.mod(Nat.add(x1, Nat.div(x0, R)), R), LS.cr_limbs(LS.carry(R, rest, Nat.div(Nat.add(x1, Nat.div(x0, R)), R)))}}, LS.cr_out(LS.carry0(R, Con{x0, Con{x1, rest}}))}) : List<&2, Nat>}:
  +xs2 = {Con{x0, Con{x1, rest}} : List<&2, Nat>}
  +s1 = Nat.add(x1, Nat.div(x0, R))
  +r = LS.carry(R, rest, Nat.div(s1, R))
  +c = LS.cr_out(LS.carry0(R, xs2))
  Equal.trans(List<&2, Nat>, LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{LS.cr_limbs(LS.carry0(R, xs2)), c}), LS.pass_fin(R, LS.Cr{Con{Nat.mod(x0, R), Con{Nat.mod(s1, R), LS.cr_limbs(r)}}, c}), PS.pass_eq(R, x0, x1, rest), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.pass_fin(R, LS.Cr{z, c}), LS.cr_limbs(LS.carry0(R, xs2)), Con{Nat.mod(x0, R), Con{Nat.mod(s1, R), LS.cr_limbs(r)}}, PS.c0_limbs(R, x0, x1, rest)))

def pass_len(+R: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}) -> {PS.ln(LS.pass(R, xs)) == 15n : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({0n == 15n : Nat}, N.zero_succ(14n, hl))
    case Con{x0, Nil{}}:
      Empty.absurd({PS.ln(LS.pass(R, Con{x0, Nil{}})) == 15n : Nat}, N.zero_succ(13n, N.succ_inj(0n, 14n, hl)))
    case Con{+x0, Con{+x1, +rest}}:
      +xs2 = {Con{x0, Con{x1, rest}} : List<&2, Nat>}
      +s1 = Nat.add(x1, Nat.div(x0, R))
      +r = LS.carry(R, rest, Nat.div(s1, R))
      +c = LS.cr_out(LS.carry0(R, xs2))
      +t = Nat.add(Nat.mod(x0, R), Nat.mul(c, 19n))
      +e0 = Equal.cong(List<&2, Nat>, Nat, z => PS.ln(z), LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{Con{Nat.mod(x0, R), Con{Nat.mod(s1, R), LS.cr_limbs(r)}}, c}), pass_shape(R, x0, x1, rest))
      +e1 = Equal.cong(Nat, Nat, z => 2n+z, PS.ln(LS.cr_limbs(r)), PS.ln(rest), carry_len(R, rest, Nat.div(s1, R)))
      tr(PS.ln(LS.pass(R, xs2)), 2n+PS.ln(LS.cr_limbs(r)), 15n, e0, tr(2n+PS.ln(LS.cr_limbs(r)), 2n+PS.ln(rest), 15n, e1, hl))

# ---- value bounds ----

def small_r(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +k: Nat, +hk: {Nat.is_le(k, 256n) == True{} : Bool}) -> {Nat.is_le(k, R) == True{} : Bool}:
  PS.at_r(one, R, hR, z => {Nat.is_le(k, z) == True{} : Bool}, SB.small_le(one, h1, k, hk, 17n, 9n, {==}))

# limbs below R: value below 2^(17 n)
def lv_lt(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hb: {FV.below(xs, R) == True{} : Bool}) -> {Nat.is_lt(FV.lv(xs), NL.sh(PS.ln(xs), one)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subst(Nat, o => {Nat.is_lt(0n, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
    case Con{+x, +t}:
      +Lt = FV.lv(t)
      +Mt = NL.sh(PS.ln(t), one)
      +ih = lv_lt(one, h1, R, hR, t, NL.below_tail(x, t, R, hb))
      +eL = sy(Nat.mul(R, Lt), C.shift(17n, Lt), CA.mul_r(one, h1, R, hR, Lt))
      +eM = CA.mul_r(one, h1, R, hR, Mt)
      +a1 = N.lt_add_r2(x, R, Nat.mul(R, Lt), NL.below_head(x, t, R, hb))
      +a2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(x, Nat.mul(R, Lt)), z) == True{} : Bool}, Nat.add(R, Nat.mul(R, Lt)), Nat.mul(R, 1n+Lt), sy(Nat.mul(R, 1n+Lt), Nat.add(R, Nat.mul(R, Lt)), NA.mul_succ(R, Lt)), a1)
      +a3 = N.lt_le_trans(Nat.add(x, Nat.mul(R, Lt)), Nat.mul(R, 1n+Lt), Nat.mul(R, Mt), a2, M.le_mul2(R, 1n+Lt, R, Mt, N.le_refl(R), N.lt_succ_le_succ(Lt, Mt, ih)))
      +a4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(x, z), Nat.mul(R, Mt)) == True{} : Bool}, Nat.mul(R, Lt), C.shift(17n, Lt), CA.mul_r(one, h1, R, hR, Lt), a3)
      L.subst(Nat, z => {Nat.is_lt(Nat.add(x, C.shift(17n, Lt)), z) == True{} : Bool}, Nat.mul(R, Mt), C.shift(17n, Mt), eM, a4)

def lv_lt15(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}, +hb: {FV.below(xs, R) == True{} : Bool}) -> {Nat.is_lt(FV.lv(xs), WD.sc(255n, one)) == True{} : Bool}:
  +e = tr(NL.sh(PS.ln(xs), one), NL.sh(15n, one), WD.sc(255n, one), Equal.cong(Nat, Nat, z => NL.sh(z, one), PS.ln(xs), 15n, hl), NL.sh15(one))
  L.subst(Nat, z => {Nat.is_lt(FV.lv(xs), z) == True{} : Bool}, NL.sh(PS.ln(xs), one), WD.sc(255n, one), e, lv_lt(one, h1, R, hR, xs, hb))

# ---- the first pass: limbs at most R, value below 2^255 + 95 ----

# 4 R + 5 <= R 5
def f_c5(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(WD.sc(19n, one), 5n), Nat.mul(R, 5n)) == True{} : Bool}:
  +e4 = tr(Nat.mul(R, 4n), WD.sc(2n, R), WD.sc(19n, one), PS.mulp(2n, R), PS.at_r(one, R, hR, z => {WD.sc(2n, z) == WD.sc(19n, one) : Nat}, M.sc_sc(2n, 17n, one)))
  +e5 = tr(Nat.mul(R, 5n), Nat.add(Nat.mul(R, 4n), R), Nat.add(WD.sc(19n, one), R), tr(Nat.mul(R, 5n), Nat.add(R, Nat.mul(R, 4n)), Nat.add(Nat.mul(R, 4n), R), NA.mul_succ(R, 4n), NA.add_comm(R, Nat.mul(R, 4n))), M.cong_l(Nat.mul(R, 4n), WD.sc(19n, one), R, e4))
  L.subst(Nat, z => {Nat.is_le(Nat.add(WD.sc(19n, one), 5n), z) == True{} : Bool}, Nat.add(WD.sc(19n, one), R), Nat.mul(R, 5n), sy(Nat.mul(R, 5n), Nat.add(WD.sc(19n, one), R), e5), N.le_add_left(5n, R, WD.sc(19n, one), small_r(one, h1, R, hR, 5n, {==})))

# the first pass on 15 limbs below 2^19
def pass1(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}, +hx: {FV.below(xs, WD.sc(19n, one)) == True{} : Bool}) -> {Bool.and(FV.below(LS.pass(R, xs), 1n+R), Nat.is_lt(FV.lv(LS.pass(R, xs)), Nat.add(WD.sc(255n, one), 95n))) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(FV.below(LS.pass(R, Nil{}), 1n+R), Nat.is_lt(FV.lv(LS.pass(R, Nil{})), Nat.add(WD.sc(255n, one), 95n))) == True{} : Bool}, N.zero_succ(14n, hl))
    case Con{x0, Nil{}}:
      Empty.absurd({Bool.and(FV.below(LS.pass(R, Con{x0, Nil{}}), 1n+R), Nat.is_lt(FV.lv(LS.pass(R, Con{x0, Nil{}})), Nat.add(WD.sc(255n, one), 95n))) == True{} : Bool}, N.zero_succ(13n, N.succ_inj(0n, 14n, hl)))
    case Con{+x0, Con{+x1, +rest}}:
      +xs2 = {Con{x0, Con{x1, rest}} : List<&2, Nat>}
      +s1 = Nat.add(x1, Nat.div(x0, R))
      +r = LS.carry(R, rest, Nat.div(s1, R))
      +K = LS.carry0(R, xs2)
      +c = LS.cr_out(K)
      +m0 = Nat.mod(x0, R)
      +m1 = Nat.mod(s1, R)
      +Lr = LS.cr_limbs(r)
      +t = Nat.add(m0, Nat.mul(c, 19n))
      +ys = {Con{m0, Con{m1, Lr}} : List<&2, Nat>}
      +ep = pass_shape(R, x0, x1, rest)
      +hk = CA.carry0_below(one, h1, R, hR, xs2, WD.sc(19n, one), 5n, hx, {==}, f_c5(one, h1, R, hR))
      +hb = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, LS.cr_limbs(K), ys, PS.c0_limbs(R, x0, x1, rest), L.and_left(FV.below(LS.cr_limbs(K), R), Nat.is_lt(c, 5n), hk))
      +hc = L.and_right(FV.below(LS.cr_limbs(K), R), Nat.is_lt(c, 5n), hk)
      +h0 = NL.below_head(m0, Con{m1, Lr}, R, hb)
      +h1b = NL.below_head(m1, Lr, R, NL.below_tail(m0, Con{m1, Lr}, R, hb))
      +hr = NL.below_tail(m1, Lr, R, NL.below_tail(m0, Con{m1, Lr}, R, hb))
      +ht19 = PS.mul_lt_r(c, 5n, 19n, {==}, hc)
      +ht = N.lt_le_trans(t, Nat.add(R, 95n), Nat.mul(R, 2n), NL.lt_add2(m0, Nat.mul(c, 19n), R, 95n, h0, ht19), L.subst(Nat, z => {Nat.is_le(Nat.add(R, 95n), z) == True{} : Bool}, Nat.add(R, R), Nat.mul(R, 2n), tr(Nat.add(R, R), Nat.add(R, Nat.mul(R, 1n)), Nat.mul(R, 2n), M.cong_r(R, R, Nat.mul(R, 1n), sy(Nat.mul(R, 1n), R, NA.mul_one(R))), sy(Nat.mul(R, 2n), Nat.add(R, Nat.mul(R, 1n)), NA.mul_succ(R, 1n))), N.le_add_left(95n, R, R, small_r(one, h1, R, hR, 95n, {==}))))
      +hd = CA.div_lt(one, h1, R, hR, t, 2n, ht)
      +hy1 = N.le_lt_trans(Nat.add(m1, Nat.div(t, R)), Nat.add(m1, 1n), 1n+R, N.le_add_left(Nat.div(t, R), 1n, m1, N.lt_succ_le(Nat.div(t, R), 1n, hd)), L.subst(Nat, z => {Nat.is_lt(z, 1n+R) == True{} : Bool}, 1n+m1, Nat.add(m1, 1n), tr(1n+m1, 1n+Nat.add(m1, 0n), Nat.add(m1, 1n), Equal.cong(Nat, Nat, z => 1n+z, m1, Nat.add(m1, 0n), sy(Nat.add(m1, 0n), m1, N.add_zero(m1))), sy(Nat.add(m1, 1n), 1n+Nat.add(m1, 0n), N.add_succ(m1, 0n))), N.lt_add_left(m1, R, 1n, h1b)))
      +hy0 = N.lt_le_trans(Nat.mod(t, R), R, 1n+R, CA.mod_lt(one, h1, R, hR, t), N.le_succ(R))
      +hbl = NL.below_con(Nat.mod(t, R), Con{Nat.add(m1, Nat.div(t, R)), Lr}, 1n+R, hy0, NL.below_con(Nat.add(m1, Nat.div(t, R)), Lr, 1n+R, hy1, NL.below_mono(Lr, R, 1n+R, N.le_succ(R), hr)))
      +hb2 = L.subst(List<&2, Nat>, z => {FV.below(z, 1n+R) == True{} : Bool}, LS.pass_fin(R, LS.Cr{ys, c}), LS.pass(R, xs2), Equal.sym(List<&2, Nat>, LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{ys, c}), ep), hbl)
      +ev = tr(FV.lv(LS.pass(R, xs2)), FV.lv(LS.pass_fin(R, LS.Cr{ys, c})), Nat.add(FV.lv(ys), Nat.mul(c, 19n)), Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{ys, c}), ep), PS.fin_val(one, h1, R, hR, m0, m1, Lr, c))
      +hlen = tr(PS.ln(ys), 2n+PS.ln(rest), 15n, Equal.cong(Nat, Nat, z => 2n+z, PS.ln(Lr), PS.ln(rest), carry_len(R, rest, Nat.div(s1, R))), hl)
      +hv0 = NL.lt_add2(FV.lv(ys), Nat.mul(c, 19n), WD.sc(255n, one), 95n, lv_lt15(one, h1, R, hR, ys, hlen, hb), ht19)
      +hv = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(WD.sc(255n, one), 95n)) == True{} : Bool}, Nat.add(FV.lv(ys), Nat.mul(c, 19n)), FV.lv(LS.pass(R, xs2)), sy(FV.lv(LS.pass(R, xs2)), Nat.add(FV.lv(ys), Nat.mul(c, 19n)), ev), hv0)
      L.and_intro(FV.below(LS.pass(R, xs2), 1n+R), Nat.is_lt(FV.lv(LS.pass(R, xs2)), Nat.add(WD.sc(255n, one), 95n)), hb2, hv)

# ---- the second pass: limbs below R ----

def lt_add_cancel(+d: Nat, +x: Nat, +y: Nat) -> {Nat.is_lt(Nat.add(d, x), Nat.add(d, y)) == Nat.is_lt(x, y) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      lt_add_cancel(e, x, y)

def div0(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +t: Nat, +h: {Nat.is_lt(t, R) == True{} : Bool}) -> {Nat.div(t, R) == 0n : Nat}:
  +b = Nat.sub(R, 1n)
  +hb = CA.r_succ(one, h1, R, hR)
  +h2 = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, R, 1n+b, sy(1n+b, R, hb), h)
  L.subst(Nat, z => {Nat.div(t, z) == 0n : Nat}, 1n+b, R, hb, NR.div_of(0n, b, t, h2))

def mod_id(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +t: Nat, +h: {Nat.is_lt(t, R) == True{} : Bool}) -> {Nat.mod(t, R) == t : Nat}:
  +b = Nat.sub(R, 1n)
  +hb = CA.r_succ(one, h1, R, hR)
  +h2 = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, R, 1n+b, sy(1n+b, R, hb), h)
  L.subst(Nat, z => {Nat.mod(t, z) == t : Nat}, 1n+b, R, hb, NR.mod_of(0n, b, t, h2))

# the new limb 0 of the second pass stays below R
def t2_lt(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +c: Nat, +m0: Nat, +Lv: Nat, +V: Nat, +hc: {Nat.is_lt(c, 2n) == True{} : Bool}, +hm: {Nat.is_le(m0, Lv) == True{} : Bool}, +hm0: {Nat.is_lt(m0, R) == True{} : Bool}, +hs: {Nat.add(Lv, WD.sc(255n, c)) == V : Nat}, +hV: {Nat.is_lt(V, Nat.add(WD.sc(255n, one), 95n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(m0, Nat.mul(c, 19n)), R) == True{} : Bool}:
  match c:
    case 0n:
      L.subst(Nat, z => {Nat.is_lt(z, R) == True{} : Bool}, m0, Nat.add(m0, 0n), sy(Nat.add(m0, 0n), m0, N.add_zero(m0)), hm0)
    case 1n+ +c2:
      +S1 = WD.sc(255n, one)
      +Sc = WD.sc(255n, 1n+c2)
      +hone = L.subst(Nat, o => {Nat.is_le(o, 1n+c2) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le_succ(0n, 1n+c2, N.le_lt_trans(0n, c2, 1n+c2, N.zero_le(c2), N.lt_succ(c2))))
      +l1 = M.le_add_r(S1, Sc, Lv, M.le_sc(255n, one, 1n+c2, hone))
      +l2 = L.subst(Nat, z => {Nat.is_le(Nat.add(S1, Lv), z) == True{} : Bool}, Nat.add(Sc, Lv), V, tr(Nat.add(Sc, Lv), Nat.add(Lv, Sc), V, NA.add_comm(Sc, Lv), hs), L.subst(Nat, z => {Nat.is_le(z, Nat.add(Sc, Lv)) == True{} : Bool}, Nat.add(S1, Lv), Nat.add(S1, Lv), {==}, l1))
      +l3 = N.le_lt_trans(Nat.add(S1, Lv), V, Nat.add(S1, 95n), l2, hV)
      +hL = Equal.trans(Bool, Nat.is_lt(Lv, 95n), Nat.is_lt(Nat.add(S1, Lv), Nat.add(S1, 95n)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(S1, Lv), Nat.add(S1, 95n)), Nat.is_lt(Lv, 95n), lt_add_cancel(S1, Lv, 95n)), l3)
      +hm95 = N.le_lt_trans(m0, Lv, 95n, hm, hL)
      +h19 = AR.mul_le(1n+c2, 1n, 19n, N.lt_succ_le(1n+c2, 1n, hc))
      +l4 = N.lt_le_trans(Nat.add(m0, Nat.mul(1n+c2, 19n)), Nat.add(95n, Nat.mul(1n+c2, 19n)), Nat.add(95n, 19n), N.lt_add_r2(m0, 95n, Nat.mul(1n+c2, 19n), hm95), N.le_add_left(Nat.mul(1n+c2, 19n), 19n, 95n, h19))
      N.lt_le_trans(Nat.add(m0, Nat.mul(1n+c2, 19n)), 114n, R, l4, small_r(one, h1, R, hR, 114n, {==}))

# R + 3 <= R 2
def f_c2(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(1n+R, 2n), Nat.mul(R, 2n)) == True{} : Bool}:
  +e2 = tr(Nat.mul(R, 2n), Nat.add(R, Nat.mul(R, 1n)), Nat.add(R, R), NA.mul_succ(R, 1n), M.cong_r(R, Nat.mul(R, 1n), R, NA.mul_one(R)))
  +e3 = tr(Nat.add(1n+R, 2n), Nat.add(R, 3n), Nat.add(R, 3n), sy(Nat.add(R, 3n), Nat.add(1n+R, 2n), tr(Nat.add(R, 3n), Nat.add(3n, R), Nat.add(1n+R, 2n), NA.add_comm(R, 3n), tr(Nat.add(3n, R), 3n+R, Nat.add(1n+R, 2n), {==}, sy(Nat.add(1n+R, 2n), 3n+R, tr(Nat.add(1n+R, 2n), 1n+Nat.add(R, 2n), 3n+R, {==}, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(R, 2n), 2n+R, tr(Nat.add(R, 2n), Nat.add(2n, R), 2n+R, NA.add_comm(R, 2n), {==}))))))), {==})
  +l = N.le_add_left(3n, R, R, small_r(one, h1, R, hR, 3n, {==}))
  L.subst(Nat, z => {Nat.is_le(z, Nat.mul(R, 2n)) == True{} : Bool}, Nat.add(R, 3n), Nat.add(1n+R, 2n), sy(Nat.add(1n+R, 2n), Nat.add(R, 3n), e3), L.subst(Nat, z => {Nat.is_le(Nat.add(R, 3n), z) == True{} : Bool}, Nat.add(R, R), Nat.mul(R, 2n), sy(Nat.mul(R, 2n), Nat.add(R, R), e2), l))

def pass2(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +ys: List<&2, Nat>, +hl: {PS.ln(ys) == 15n : Nat}, +hy: {FV.below(ys, 1n+R) == True{} : Bool}, +hv: {Nat.is_lt(FV.lv(ys), Nat.add(WD.sc(255n, one), 95n)) == True{} : Bool}) -> {FV.below(LS.pass(R, ys), R) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({FV.below(LS.pass(R, Nil{}), R) == True{} : Bool}, N.zero_succ(14n, hl))
    case Con{y0, Nil{}}:
      Empty.absurd({FV.below(LS.pass(R, Con{y0, Nil{}}), R) == True{} : Bool}, N.zero_succ(13n, N.succ_inj(0n, 14n, hl)))
    case Con{+y0, Con{+y1, +rest}}:
      +ys2 = {Con{y0, Con{y1, rest}} : List<&2, Nat>}
      +s1 = Nat.add(y1, Nat.div(y0, R))
      +r = LS.carry(R, rest, Nat.div(s1, R))
      +K = LS.carry0(R, ys2)
      +c = LS.cr_out(K)
      +m0 = Nat.mod(y0, R)
      +m1 = Nat.mod(s1, R)
      +Lr = LS.cr_limbs(r)
      +t = Nat.add(m0, Nat.mul(c, 19n))
      +zs = {Con{m0, Con{m1, Lr}} : List<&2, Nat>}
      +ep = pass_shape(R, y0, y1, rest)
      +hk = CA.carry0_below(one, h1, R, hR, ys2, 1n+R, 2n, hy, {==}, f_c2(one, h1, R, hR))
      +el = PS.c0_limbs(R, y0, y1, rest)
      +hb = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, LS.cr_limbs(K), zs, el, L.and_left(FV.below(LS.cr_limbs(K), R), Nat.is_lt(c, 2n), hk))
      +hc = L.and_right(FV.below(LS.cr_limbs(K), R), Nat.is_lt(c, 2n), hk)
      +h0 = NL.below_head(m0, Con{m1, Lr}, R, hb)
      +h1b = NL.below_head(m1, Lr, R, NL.below_tail(m0, Con{m1, Lr}, R, hb))
      +hr = NL.below_tail(m1, Lr, R, NL.below_tail(m0, Con{m1, Lr}, R, hb))
      +ecv = CA.carry0_val(one, h1, R, hR, ys2)
      +esh = tr(CA.shl(ys2, c), NL.sh(15n, c), WD.sc(255n, c), tr(CA.shl(ys2, c), NL.sh(PS.ln(ys2), c), NL.sh(15n, c), PS.shl_sh(ys2, c), Equal.cong(Nat, Nat, z => NL.sh(z, c), PS.ln(ys2), 15n, hl)), NL.sh15(c))
      +eLv = Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), LS.cr_limbs(K), zs, el)
      +hs = tr(Nat.add(FV.lv(zs), WD.sc(255n, c)), Nat.add(FV.lv(LS.cr_limbs(K)), CA.shl(ys2, c)), FV.lv(ys2), M.cong_add(FV.lv(zs), FV.lv(LS.cr_limbs(K)), WD.sc(255n, c), CA.shl(ys2, c), sy(FV.lv(LS.cr_limbs(K)), FV.lv(zs), eLv), sy(CA.shl(ys2, c), WD.sc(255n, c), esh)), ecv)
      +ht = t2_lt(one, h1, R, hR, c, m0, FV.lv(zs), FV.lv(ys2), hc, N.le_add_right(m0, C.shift(17n, FV.lv(Con{m1, Lr}))), h0, hs, hv)
      +ed = div0(one, h1, R, hR, t, ht)
      +hy1 = L.subst(Nat, z => {Nat.is_lt(z, R) == True{} : Bool}, m1, Nat.add(m1, Nat.div(t, R)), tr(m1, Nat.add(m1, 0n), Nat.add(m1, Nat.div(t, R)), sy(Nat.add(m1, 0n), m1, N.add_zero(m1)), M.cong_r(m1, 0n, Nat.div(t, R), sy(Nat.div(t, R), 0n, ed))), h1b)
      +hbl = NL.below_con(Nat.mod(t, R), Con{Nat.add(m1, Nat.div(t, R)), Lr}, R, CA.mod_lt(one, h1, R, hR, t), NL.below_con(Nat.add(m1, Nat.div(t, R)), Lr, R, hy1, hr))
      L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, LS.pass_fin(R, LS.Cr{zs, c}), LS.pass(R, ys2), Equal.sym(List<&2, Nat>, LS.pass(R, ys2), LS.pass_fin(R, LS.Cr{zs, c}), ep), hbl)

# ---- the conditional subtraction ----

def mlc_go(+q: Nat, +k: Nat, +S: Nat, +h: {Nat.is_lt(Nat.mul(q, S), Nat.mul(k, S)) == True{} : Bool}, o: Or({Nat.is_lt(q, k) == True{} : Bool}, {Nat.is_lt(q, k) == False{} : Bool})) -> {Nat.is_lt(q, k) == True{} : Bool}:
  match o:
    case Inl{e}:
      e
    case Inr{e}:
      +a = AR.mul_le(k, q, S, N.not_lt_le(q, k, e))
      Empty.absurd({Nat.is_lt(q, k) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(q, S), Nat.mul(q, S)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.mul(q, S), Nat.mul(q, S)), False{}, N.lt_irrefl(Nat.mul(q, S))), N.lt_le_trans(Nat.mul(q, S), Nat.mul(k, S), Nat.mul(q, S), h, a))))

def mul_lt_cancel(+q: Nat, +k: Nat, +S: Nat, +h: {Nat.is_lt(Nat.mul(q, S), Nat.mul(k, S)) == True{} : Bool}) -> {Nat.is_lt(q, k) == True{} : Bool}:
  mlc_go(q, k, S, h, L.bool_cases(Nat.is_lt(q, k)))

def csub_eta(+r: LS.Cr, +zs: List<&2, Nat>) -> {LS.csub_fin(r, zs) == LS.sel(LS.cr_out(r), zs, LS.cr_limbs(r)) : List<&2, Nat>}:
  match r:
    case LS.Cr{a, c}:
      {==}

# p != 19 (p + 19 = 2^255 >= 64 > 38)
def ne_go(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, o: Or({Nat.is_eq(19n, 1n+pp) == True{} : Bool}, {Nat.is_eq(19n, 1n+pp) == False{} : Bool})) -> {Nat.is_eq(19n, 1n+pp) == False{} : Bool}:
  match o:
    case Inr{e}:
      e
    case Inl{e}:
      +eq = N.eq_from_is_eq(19n, 1n+pp, e)
      +a = L.subst(Nat, z => {Nat.add(z, 19n) == WD.sc(255n, one) : Nat}, 1n+pp, 19n, sy(19n, 1n+pp, eq), hP)
      +b = L.subst(Nat, o => {Nat.is_lt(38n, WD.sc(255n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_le_trans(38n, WD.sc(6n, 1n), WD.sc(255n, 1n), {==}, M.sc_mono(249n, 6n, 1n)))
      +c = L.subst(Nat, z => {Nat.is_lt(38n, z) == True{} : Bool}, WD.sc(255n, one), Nat.add(19n, 19n), sy(Nat.add(19n, 19n), WD.sc(255n, one), a), b)
      Empty.absurd({Nat.is_eq(19n, 1n+pp) == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(38n, 38n), True{}, {==}, c)))

def match_ne(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.is_eq(19n, 1n+pp) == False{} : Bool}:
  ne_go(one, h1, pp, hP, L.bool_cases(Nat.is_eq(19n, 1n+pp)))

# 19 < p
def p19(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.is_lt(19n, 1n+pp) == True{} : Bool}:
  +S1 = WD.sc(255n, one)
  +a = L.subst(Nat, o => {Nat.is_le(38n, WD.sc(255n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.le_trans(38n, WD.sc(6n, 1n), WD.sc(255n, 1n), {==}, M.sc_mono(249n, 6n, 1n)))
  +b = L.subst(Nat, z => {Nat.is_le(38n, z) == True{} : Bool}, S1, Nat.add(1n+pp, 19n), sy(Nat.add(1n+pp, 19n), S1, hP), a)
  +c = L.subst(Nat, z => {Nat.is_le(z, Nat.add(1n+pp, 19n)) == True{} : Bool}, 38n, Nat.add(19n, 19n), {==}, b)
  +d = L.subst(Nat, z => {Nat.is_le(Nat.add(19n, 19n), z) == True{} : Bool}, Nat.add(1n+pp, 19n), Nat.add(19n, 1n+pp), NA.add_comm(1n+pp, 19n), c)
  +e = Equal.trans(Bool, Nat.is_le(19n, 1n+pp), Nat.is_le(Nat.add(19n, 19n), Nat.add(19n, 1n+pp)), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(19n, 19n), Nat.add(19n, 1n+pp)), Nat.is_le(19n, 1n+pp), NR.le_add_cancel(19n, 19n, 1n+pp)), d)
  N.lt_or_eq(19n, 1n+pp, e, match_ne(one, h1, pp, hP))


def lt_cancel19(+x: Nat, +P: Nat, +h: {Nat.is_lt(Nat.add(x, 19n), Nat.add(P, 19n)) == True{} : Bool}) -> {Nat.is_lt(x, P) == True{} : Bool}:
  +h2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(P, 19n)) == True{} : Bool}, Nat.add(x, 19n), Nat.add(19n, x), NA.add_comm(x, 19n), h)
  +h3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(19n, x), z) == True{} : Bool}, Nat.add(P, 19n), Nat.add(19n, P), NA.add_comm(P, 19n), h2)
  Equal.trans(Bool, Nat.is_lt(x, P), Nat.is_lt(Nat.add(19n, x), Nat.add(19n, P)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(19n, x), Nat.add(19n, P)), Nat.is_lt(x, P), lt_add_cancel(19n, x, P)), h3)

def eq_cancel19(+x: Nat, +y: Nat, +h: {Nat.add(x, 19n) == Nat.add(y, 19n) : Nat}) -> {x == y : Nat}:
  NR.add_cancel(19n, x, y, tr(Nat.add(19n, x), Nat.add(x, 19n), Nat.add(19n, y), NA.add_comm(19n, x), tr(Nat.add(x, 19n), Nat.add(y, 19n), Nat.add(19n, y), h, NA.add_comm(y, 19n))))

def csub_one(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +q2: Nat, +ls: List<&2, Nat>, +zs: List<&2, Nat>, +hq: {Nat.is_lt(1n+q2, 2n) == True{} : Bool}, +hs: {Nat.add(FV.lv(ls), Nat.mul(1n+q2, WD.sc(255n, one))) == Nat.add(FV.lv(zs), 19n) : Nat}, +hls: {FV.below(ls, R) == True{} : Bool}, +hzs: {FV.below(zs, R) == True{} : Bool}, +hlz: {PS.ln(zs) == 15n : Nat}, +hll: {PS.ln(ls) == 15n : Nat}) -> {Bool.and(Bool.and(FV.below(LS.sel(1n+q2, zs, ls), R), Nat.is_lt(FV.lv(LS.sel(1n+q2, zs, ls)), 1n+pp)), Nat.is_eq(FV.lv(LS.sel(1n+q2, zs, ls)), Nat.mod(FV.lv(zs), 1n+pp))) == True{} : Bool}:
  match q2:
    case 1n+q3:
      Empty.absurd({Bool.and(Bool.and(FV.below(LS.sel(2n+q3, zs, ls), R), Nat.is_lt(FV.lv(LS.sel(2n+q3, zs, ls)), 1n+pp)), Nat.is_eq(FV.lv(LS.sel(2n+q3, zs, ls)), Nat.mod(FV.lv(zs), 1n+pp))) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(q3, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q3, 0n), False{}, N.not_lt_zero(q3)), hq)))
    case 0n:
      +P = {1n+pp : Nat}
      +S1 = WD.sc(255n, one)
      +Z = FV.lv(zs)
      +Ls = FV.lv(ls)
      +hZ = lv_lt15(one, h1, R, hR, zs, hlz, hzs)
      +hs1 = tr(Nat.add(Ls, S1), Nat.add(Ls, Nat.add(S1, 0n)), Nat.add(Z, 19n), M.cong_r(Ls, S1, Nat.add(S1, 0n), sy(Nat.add(S1, 0n), S1, N.add_zero(S1))), hs)
      +e1 = tr(Nat.add(Nat.add(Ls, P), 19n), Nat.add(Ls, Nat.add(P, 19n)), Nat.add(Z, 19n), NA.add_assoc(Ls, P, 19n), tr(Nat.add(Ls, Nat.add(P, 19n)), Nat.add(Ls, S1), Nat.add(Z, 19n), M.cong_r(Ls, Nat.add(P, 19n), S1, hP), hs1))
      +eZ = eq_cancel19(Nat.add(Ls, P), Z, e1)
      +hLP0 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(P, 19n)) == True{} : Bool}, Z, Nat.add(Ls, P), sy(Nat.add(Ls, P), Z, eZ), L.subst(Nat, z => {Nat.is_lt(Z, z) == True{} : Bool}, S1, Nat.add(P, 19n), sy(Nat.add(P, 19n), S1, hP), hZ))
      +hL19 = Equal.trans(Bool, Nat.is_lt(Ls, 19n), Nat.is_lt(Nat.add(P, Ls), Nat.add(P, 19n)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(P, Ls), Nat.add(P, 19n)), Nat.is_lt(Ls, 19n), lt_add_cancel(P, Ls, 19n)), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(P, 19n)) == True{} : Bool}, Nat.add(Ls, P), Nat.add(P, Ls), NA.add_comm(Ls, P), hLP0))
      +hLP = N.lt_trans(Ls, 19n, P, hL19, p19(one, h1, pp, hP))
      +emod = tr(Nat.mod(Z, P), Nat.mod(Nat.add(Nat.mul(1n, P), Ls), P), Ls, Equal.cong(Nat, Nat, z => Nat.mod(z, P), Z, Nat.add(Nat.mul(1n, P), Ls), tr(Z, Nat.add(Ls, P), Nat.add(Nat.mul(1n, P), Ls), sy(Nat.add(Ls, P), Z, eZ), tr(Nat.add(Ls, P), Nat.add(P, Ls), Nat.add(Nat.mul(1n, P), Ls), NA.add_comm(Ls, P), M.cong_l(P, Nat.mul(1n, P), Ls, sy(Nat.mul(1n, P), P, AR.one_mul(P)))))), NR.mod_of(1n, pp, Ls, hLP))
      +leq = tr(PS.ln(zs), 15n, PS.ln(ls), hlz, sy(PS.ln(ls), 15n, hll))
      +esel = OP.sel1(zs, ls, leq)
      +goal = L.and_intro(Bool.and(FV.below(ls, R), Nat.is_lt(Ls, P)), Nat.is_eq(Ls, Nat.mod(Z, P)), L.and_intro(FV.below(ls, R), Nat.is_lt(Ls, P), hls, hLP), L.subst(Nat, z => {Nat.is_eq(Ls, z) == True{} : Bool}, Ls, Nat.mod(Z, P), sy(Nat.mod(Z, P), Ls, emod), N.is_eq_refl(Ls)))
      L.subst(List<&2, Nat>, z => {Bool.and(Bool.and(FV.below(z, R), Nat.is_lt(FV.lv(z), P)), Nat.is_eq(FV.lv(z), Nat.mod(Z, P))) == True{} : Bool}, ls, LS.sel(1n, zs, ls), Equal.sym(List<&2, Nat>, LS.sel(1n, zs, ls), ls, esel), goal)

# q is 0 or 1: the selected limbs are canonical, their value is value(zs) mod p
def csub_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +q: Nat, +ls: List<&2, Nat>, +zs: List<&2, Nat>, +hq: {Nat.is_lt(q, 2n) == True{} : Bool}, +hs: {Nat.add(FV.lv(ls), Nat.mul(q, WD.sc(255n, one))) == Nat.add(FV.lv(zs), 19n) : Nat}, +hls: {FV.below(ls, R) == True{} : Bool}, +hzs: {FV.below(zs, R) == True{} : Bool}, +hlz: {PS.ln(zs) == 15n : Nat}, +hll: {PS.ln(ls) == 15n : Nat}) -> {Bool.and(Bool.and(FV.below(LS.sel(q, zs, ls), R), Nat.is_lt(FV.lv(LS.sel(q, zs, ls)), 1n+pp)), Nat.is_eq(FV.lv(LS.sel(q, zs, ls)), Nat.mod(FV.lv(zs), 1n+pp))) == True{} : Bool}:
  match q:
    case 0n:
      +P = {1n+pp : Nat}
      +S1 = WD.sc(255n, one)
      +Z = FV.lv(zs)
      +Ls = FV.lv(ls)
      +hL = lv_lt15(one, h1, R, hR, ls, hll, hls)
      +eS = sy(Nat.add(P, 19n), S1, hP)
      +leq = tr(PS.ln(zs), 15n, PS.ln(ls), hlz, sy(PS.ln(ls), 15n, hll))
      +e0 = tr(Ls, Nat.add(Ls, 0n), Nat.add(Z, 19n), sy(Nat.add(Ls, 0n), Ls, N.add_zero(Ls)), hs)
      +hZP = lt_cancel19(Z, P, L.subst(Nat, z => {Nat.is_lt(z, Nat.add(P, 19n)) == True{} : Bool}, Ls, Nat.add(Z, 19n), e0, L.subst(Nat, z => {Nat.is_lt(Ls, z) == True{} : Bool}, S1, Nat.add(P, 19n), eS, hL)))
      +esel = OP.sel0(zs, ls, leq)
      +emod = sy(Nat.mod(Z, P), Z, NR.mod_of(0n, pp, Z, hZP))
      +goal = L.and_intro(Bool.and(FV.below(zs, R), Nat.is_lt(Z, P)), Nat.is_eq(Z, Nat.mod(Z, P)), L.and_intro(FV.below(zs, R), Nat.is_lt(Z, P), hzs, hZP), L.subst(Nat, z => {Nat.is_eq(Z, z) == True{} : Bool}, Z, Nat.mod(Z, P), emod, N.is_eq_refl(Z)))
      L.subst(List<&2, Nat>, z => {Bool.and(Bool.and(FV.below(z, R), Nat.is_lt(FV.lv(z), P)), Nat.is_eq(FV.lv(z), Nat.mod(Z, P))) == True{} : Bool}, zs, LS.sel(0n, zs, ls), Equal.sym(List<&2, Nat>, LS.sel(0n, zs, ls), zs, esel), goal)
    case 1n+ +q2:
      csub_one(one, h1, pp, hP, R, hR, q2, ls, zs, hq, hs, hls, hzs, hlz, hll)


# ---- freeze ----

def f_c20(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(R, 20n), Nat.mul(R, 20n)) == True{} : Bool}:
  +a = N.le_trans(20n, R, Nat.mul(R, 19n), small_r(one, h1, R, hR, 20n, {==}), L.subst(Nat, z => {Nat.is_le(z, Nat.mul(R, 19n)) == True{} : Bool}, Nat.mul(R, 1n), R, NA.mul_one(R), PW.mul_le_r(R, 1n, 19n, {==})))
  L.subst(Nat, z => {Nat.is_le(Nat.add(R, 20n), z) == True{} : Bool}, Nat.add(R, Nat.mul(R, 19n)), Nat.mul(R, 20n), sy(Nat.mul(R, 20n), Nat.add(R, Nat.mul(R, 19n)), NA.mul_succ(R, 19n)), N.le_add_left(20n, Nat.mul(R, 19n), R, a))

def freeze_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}, +hx: {FV.below(xs, WD.sc(19n, one)) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(LS.freeze_l(R, xs), R), Nat.is_lt(FV.lv(LS.freeze_l(R, xs)), 1n+pp)), Nat.is_eq(FV.lv(LS.freeze_l(R, xs)), Nat.mod(FV.lv(xs), 1n+pp))) == True{} : Bool}:
  +P = {1n+pp : Nat}
  +S1 = WD.sc(255n, one)
  +y = LS.pass(R, xs)
  +z = LS.pass(R, y)
  +p1 = pass1(one, h1, R, hR, xs, hl, hx)
  +hly = pass_len(R, xs, hl)
  +hlz = pass_len(R, y, hly)
  +hz = pass2(one, h1, R, hR, y, hly, L.and_left(FV.below(y, 1n+R), Nat.is_lt(FV.lv(y), Nat.add(S1, 95n)), p1), L.and_right(FV.below(y, 1n+R), Nat.is_lt(FV.lv(y), Nat.add(S1, 95n)), p1))
  +r = LS.carry(R, z, 19n)
  +ls = LS.cr_limbs(r)
  +q = LS.cr_out(r)
  +cv = CA.carry_val(one, h1, R, hR, z, 19n)
  +esh = tr(CA.shl(z, q), WD.sc(255n, q), Nat.mul(q, S1), tr(CA.shl(z, q), NL.sh(15n, q), WD.sc(255n, q), tr(CA.shl(z, q), NL.sh(PS.ln(z), q), NL.sh(15n, q), PS.shl_sh(z, q), Equal.cong(Nat, Nat, t => NL.sh(t, q), PS.ln(z), 15n, hlz)), NL.sh15(q)), sy(Nat.mul(q, S1), WD.sc(255n, q), AR.mul_sc1(255n, one, h1, q)))
  +hs = tr(Nat.add(FV.lv(ls), Nat.mul(q, S1)), Nat.add(FV.lv(ls), CA.shl(z, q)), Nat.add(FV.lv(z), 19n), M.cong_r(FV.lv(ls), Nat.mul(q, S1), CA.shl(z, q), sy(CA.shl(z, q), Nat.mul(q, S1), esh)), cv)
  +hcb = CA.carry_below(one, h1, R, hR, z, 19n, R, 20n, hz, {==}, f_c20(one, h1, R, hR))
  +hls = L.and_left(FV.below(ls, R), Nat.is_lt(q, 20n), hcb)
  +hll = tr(PS.ln(ls), PS.ln(z), 15n, carry_len(R, z, 19n), hlz)
  +hPS = L.subst(Nat, t => {Nat.is_le(P, t) == True{} : Bool}, Nat.add(P, 19n), S1, hP, N.le_add_right(P, 19n))
  +h19 = N.le_trans(19n, P, S1, N.lt_le(19n, P, p19(one, h1, pp, hP)), hPS)
  +hzS = lv_lt15(one, h1, R, hR, z, hlz, hz)
  +e2S = tr(Nat.add(S1, S1), Nat.add(S1, Nat.mul(1n, S1)), Nat.mul(2n, S1), M.cong_r(S1, S1, Nat.mul(1n, S1), sy(Nat.mul(1n, S1), S1, AR.one_mul(S1))), {==})
  +hq0 = N.le_lt_trans(Nat.mul(q, S1), Nat.add(FV.lv(z), 19n), Nat.mul(2n, S1), L.subst(Nat, t => {Nat.is_le(Nat.mul(q, S1), t) == True{} : Bool}, Nat.add(FV.lv(ls), Nat.mul(q, S1)), Nat.add(FV.lv(z), 19n), hs, NL.le_add_l(FV.lv(ls), Nat.mul(q, S1))), L.subst(Nat, t => {Nat.is_lt(Nat.add(FV.lv(z), 19n), t) == True{} : Bool}, Nat.add(S1, S1), Nat.mul(2n, S1), e2S, N.lt_le_trans(Nat.add(FV.lv(z), 19n), Nat.add(S1, 19n), Nat.add(S1, S1), N.lt_add_r2(FV.lv(z), S1, 19n, hzS), N.le_add_left(19n, S1, S1, h19))))
  +hq = mul_lt_cancel(q, 2n, S1, hq0)
  +cs = csub_val(one, h1, pp, hP, R, hR, q, ls, z, hq, hs, hls, hz, hlz, hll)
  +ez = G.c_trans(pp, FV.lv(z), FV.lv(y), FV.lv(xs), PS.pass_c(one, h1, pp, hP, R, hR, y, hly), PS.pass_c(one, h1, pp, hP, R, hR, xs, hl))
  +cs2 = L.subst(Nat, t => {Bool.and(Bool.and(FV.below(LS.sel(q, z, ls), R), Nat.is_lt(FV.lv(LS.sel(q, z, ls)), P)), Nat.is_eq(FV.lv(LS.sel(q, z, ls)), t)) == True{} : Bool}, Nat.mod(FV.lv(z), P), Nat.mod(FV.lv(xs), P), ez, cs)
  L.subst(List<&2, Nat>, t => {Bool.and(Bool.and(FV.below(t, R), Nat.is_lt(FV.lv(t), P)), Nat.is_eq(FV.lv(t), Nat.mod(FV.lv(xs), P))) == True{} : Bool}, LS.sel(q, z, ls), LS.freeze_l(R, xs), Equal.sym(List<&2, Nat>, LS.freeze_l(R, xs), LS.sel(q, z, ls), csub_eta(r, z)), cs2)
