import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./nl.bend as NL
import ./pw.bend as PW
import ./carry.bend as CA
import ./pass.bend as PS

# The carry of add and sub (src/crypto/curve25519/limbs.bend pc): every
# carry moved one limb up at once, the top one re-entering limb 0 times 19.
# It keeps the value mod p, and limbs below 2^21 come back below 2^19.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# value(limbs) + 2^(17 n) out == value(xs) + c
def pcs_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +c: Nat) -> {Nat.add(FV.lv(CA.cl(LS.pcs(R, xs, c))), CA.shl(xs, CA.cc(LS.pcs(R, xs, c)))) == Nat.add(FV.lv(xs), c) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +d = Nat.div(h, R)
      +m = Nat.mod(h, R)
      +l = Nat.add(m, c)
      +r = LS.pcs(R, t, d)
      +A = FV.lv(CA.cl(r))
      +B = CA.shl(t, CA.cc(r))
      +T = FV.lv(t)
      +ec = M.cong_add(FV.lv(CA.cl(LS.cr_con(l, r))), FV.lv(Con{l, CA.cl(r)}), CA.shl(Con{h, t}, CA.cc(LS.cr_con(l, r))), C.shift(17n, B), Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), CA.cl(LS.cr_con(l, r)), Con{l, CA.cl(r)}, CA.cl_con(l, r)), M.cong_sc(17n, CA.shl(t, CA.cc(LS.cr_con(l, r))), B, Equal.cong(Nat, Nat, z => CA.shl(t, z), CA.cc(LS.cr_con(l, r)), CA.cc(r), CA.cc_con(l, r))))
      +eg = CA.regroup(l, A, B, T, d, pcs_val(one, h1, R, hR, t, d))
      +SD = C.shift(17n, d)
      +ST = C.shift(17n, T)
      +es = M.cong_l(Nat.add(l, SD), Nat.add(Nat.add(m, SD), c), ST, CA.swap3(m, c, SD))
      +ed = M.cong_l(Nat.add(Nat.add(m, SD), c), Nat.add(h, c), ST, M.cong_l(Nat.add(m, SD), h, c, CA.dm(one, h1, R, hR, h)))
      tr(Nat.add(FV.lv(CA.cl(LS.cr_con(l, r))), CA.shl(Con{h, t}, CA.cc(LS.cr_con(l, r)))), Nat.add(Nat.add(l, C.shift(17n, A)), C.shift(17n, B)), Nat.add(Nat.add(h, ST), c), ec,
        tr(Nat.add(Nat.add(l, C.shift(17n, A)), C.shift(17n, B)), Nat.add(Nat.add(l, SD), ST), Nat.add(Nat.add(h, ST), c), eg,
          tr(Nat.add(Nat.add(l, SD), ST), Nat.add(Nat.add(Nat.add(m, SD), c), ST), Nat.add(Nat.add(h, ST), c), es,
            tr(Nat.add(Nat.add(Nat.add(m, SD), c), ST), Nat.add(Nat.add(h, c), ST), Nat.add(Nat.add(h, ST), c), ed, CA.swap3(h, c, ST)))))

# limbs below A <= R E, carry in below E: limbs below R + E, carry out below E
def pcs_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +c: Nat, +A: Nat, +E: Nat, +hx: {FV.below(xs, A) == True{} : Bool}, +hc: {Nat.is_lt(c, E) == True{} : Bool}, +hAE: {Nat.is_le(A, Nat.mul(R, E)) == True{} : Bool}) -> {Bool.and(FV.below(CA.cl(LS.pcs(R, xs, c)), Nat.add(R, E)), Nat.is_lt(CA.cc(LS.pcs(R, xs, c)), E)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hc
    case Con{+h, +t}:
      +d = Nat.div(h, R)
      +m = Nat.mod(h, R)
      +l = Nat.add(m, c)
      +r = LS.pcs(R, t, d)
      +RE = Nat.add(R, E)
      +hh = N.lt_le_trans(h, A, Nat.mul(R, E), NL.below_head(h, t, A, hx), hAE)
      +ih = pcs_below(one, h1, R, hR, t, d, A, E, NL.below_tail(h, t, A, hx), CA.div_lt(one, h1, R, hR, h, E, hh), hAE)
      +hl = L.and_left(FV.below(CA.cl(r), RE), Nat.is_lt(CA.cc(r), E), ih)
      +ho = L.and_right(FV.below(CA.cl(r), RE), Nat.is_lt(CA.cc(r), E), ih)
      +bl = L.subst(List<&2, Nat>, z => {FV.below(z, RE) == True{} : Bool}, Con{l, CA.cl(r)}, CA.cl(LS.cr_con(l, r)), Equal.sym(List<&2, Nat>, CA.cl(LS.cr_con(l, r)), Con{l, CA.cl(r)}, CA.cl_con(l, r)), NL.below_con(l, CA.cl(r), RE, NL.lt_add2(m, c, R, E, CA.mod_lt(one, h1, R, hR, h), hc), hl))
      +bo = L.subst(Nat, z => {Nat.is_lt(z, E) == True{} : Bool}, CA.cc(r), CA.cc(LS.cr_con(l, r)), sy(CA.cc(LS.cr_con(l, r)), CA.cc(r), CA.cc_con(l, r)), ho)
      L.and_intro(FV.below(CA.cl(LS.cr_con(l, r)), RE), Nat.is_lt(CA.cc(LS.cr_con(l, r)), E), bl, bo)

def pcfin_eq(+m: Nat, +r: LS.Cr) -> {LS.pc_fin(m, r) == Con{Nat.add(m, Nat.mul(CA.cc(r), 19n)), CA.cl(r)} : List<&2, Nat>}:
  match r:
    case LS.Cr{a, q}:
      {==}

# pc keeps the value mod p (15 limbs)
def pc_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}) -> G.ceq(pp, FV.lv(LS.pc(R, xs)), FV.lv(xs)):
  match xs:
    case Nil{}:
      Empty.absurd(G.ceq(pp, 0n, 0n), N.zero_succ(14n, hl))
    case Con{+x0, +xt}:
      +d0 = Nat.div(x0, R)
      +m0 = Nat.mod(x0, R)
      +r = LS.pcs(R, xt, d0)
      +q = CA.cc(r)
      +Lv = FV.lv(CA.cl(r))
      +X = FV.lv(xt)
      +S = CA.shl(xt, q)
      +Q = WD.sc(255n, q)
      +e0 = Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), LS.pc_fin(m0, r), Con{Nat.add(m0, Nat.mul(q, 19n)), CA.cl(r)}, pcfin_eq(m0, r))
      +ev = pcs_val(one, h1, R, hR, xt, d0)
      +esh = tr(C.shift(17n, S), C.shift(17n, NL.sh(14n, q)), Q, M.cong_sc(17n, S, NL.sh(14n, q), tr(S, NL.sh(PS.ln(xt), q), NL.sh(14n, q), PS.shl_sh(xt, q), Equal.cong(Nat, Nat, z => NL.sh(z, q), PS.ln(xt), 14n, N.succ_inj(PS.ln(xt), 14n, hl)))), NL.sh15(q))
      +ex1 = M.cong_l(x0, Nat.add(m0, C.shift(17n, d0)), C.shift(17n, X), sy(Nat.add(m0, C.shift(17n, d0)), x0, CA.dm(one, h1, R, hR, x0)))
      +ex2 = tr(Nat.add(Nat.add(m0, C.shift(17n, d0)), C.shift(17n, X)), Nat.add(m0, Nat.add(C.shift(17n, d0), C.shift(17n, X))), Nat.add(m0, C.shift(17n, Nat.add(X, d0))), NA.add_assoc(m0, C.shift(17n, d0), C.shift(17n, X)), M.cong_r(m0, Nat.add(C.shift(17n, d0), C.shift(17n, X)), C.shift(17n, Nat.add(X, d0)), tr(Nat.add(C.shift(17n, d0), C.shift(17n, X)), Nat.add(C.shift(17n, X), C.shift(17n, d0)), C.shift(17n, Nat.add(X, d0)), NA.add_comm(C.shift(17n, d0), C.shift(17n, X)), M.sc_add(17n, X, d0))))
      +ex3 = M.cong_r(m0, C.shift(17n, Nat.add(X, d0)), C.shift(17n, Nat.add(Lv, S)), M.cong_sc(17n, Nat.add(X, d0), Nat.add(Lv, S), sy(Nat.add(Lv, S), Nat.add(X, d0), ev)))
      +ex4 = M.cong_r(m0, C.shift(17n, Nat.add(Lv, S)), Nat.add(C.shift(17n, Lv), Q), tr(C.shift(17n, Nat.add(Lv, S)), Nat.add(C.shift(17n, Lv), C.shift(17n, S)), Nat.add(C.shift(17n, Lv), Q), sy(Nat.add(C.shift(17n, Lv), C.shift(17n, S)), C.shift(17n, Nat.add(Lv, S)), M.sc_add(17n, Lv, S)), M.cong_r(C.shift(17n, Lv), C.shift(17n, S), Q, esh)))
      +XS = Nat.add(x0, C.shift(17n, X))
      +ex = tr(XS, Nat.add(Nat.add(m0, C.shift(17n, d0)), C.shift(17n, X)), Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), ex1, tr(Nat.add(Nat.add(m0, C.shift(17n, d0)), C.shift(17n, X)), Nat.add(m0, C.shift(17n, Nat.add(X, d0))), Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), ex2, tr(Nat.add(m0, C.shift(17n, Nat.add(X, d0))), Nat.add(m0, C.shift(17n, Nat.add(Lv, S))), Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), ex3, ex4)))
      +ep = tr(Nat.add(Nat.add(m0, Nat.mul(q, 19n)), C.shift(17n, Lv)), Nat.add(m0, Nat.add(Nat.mul(q, 19n), C.shift(17n, Lv))), Nat.add(m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n))), NA.add_assoc(m0, Nat.mul(q, 19n), C.shift(17n, Lv)), M.cong_r(m0, Nat.add(Nat.mul(q, 19n), C.shift(17n, Lv)), Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n)), NA.add_comm(Nat.mul(q, 19n), C.shift(17n, Lv))))
      +c1 = G.c_add(pp, m0, m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n)), Nat.add(C.shift(17n, Lv), Q), G.c_refl(pp, m0), G.c_add(pp, C.shift(17n, Lv), C.shift(17n, Lv), Nat.mul(q, 19n), Q, G.c_refl(pp, C.shift(17n, Lv)), G.c_sym(pp, Q, Nat.mul(q, 19n), PS.c19(one, h1, pp, hP, q))))
      G.c_trans(pp, FV.lv(LS.pc_fin(m0, r)), Nat.add(m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n))), XS, G.c_eq(pp, FV.lv(LS.pc_fin(m0, r)), Nat.add(m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n))), tr(FV.lv(LS.pc_fin(m0, r)), Nat.add(Nat.add(m0, Nat.mul(q, 19n)), C.shift(17n, Lv)), Nat.add(m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n))), e0, ep)), G.c_trans(pp, Nat.add(m0, Nat.add(C.shift(17n, Lv), Nat.mul(q, 19n))), Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), XS, c1, G.c_eq(pp, Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), XS, sy(XS, Nat.add(m0, Nat.add(C.shift(17n, Lv), Q)), ex))))

# 19 2^4 <= 2^9
def e19(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(Nat.mul(WD.sc(4n, one), 19n), WD.sc(9n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_le(Nat.mul(WD.sc(4n, o), 19n), WD.sc(9n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# R + 2^9 <= 2^19
def r9(+one: Nat, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(R, WD.sc(9n, one)), WD.sc(19n, one)) == True{} : Bool}:
  +a = PW.add_le_dbl(WD.sc(17n, one), WD.sc(9n, one), 17n, one, N.le_refl(WD.sc(17n, one)), PW.le_sc(8n, 9n, one))
  +b = N.le_trans(Nat.add(WD.sc(17n, one), WD.sc(9n, one)), WD.sc(18n, one), WD.sc(19n, one), a, PW.le_sc(1n, 18n, one))
  PS.at_r(one, R, hR, z => {Nat.is_le(Nat.add(z, WD.sc(9n, one)), WD.sc(19n, one)) == True{} : Bool}, b)

# limbs below 2^21 -> limbs below 2^19 (15 limbs)
def pc_ok21(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}, +hx: {FV.below(xs, WD.sc(21n, one)) == True{} : Bool}) -> {FV.below(LS.pc(R, xs), WD.sc(19n, one)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({True{} == True{} : Bool}, N.zero_succ(14n, hl))
    case Con{+x0, +xt}:
      +A = WD.sc(21n, one)
      +E = WD.sc(4n, one)
      +B = WD.sc(19n, one)
      +S9 = WD.sc(9n, one)
      +d0 = Nat.div(x0, R)
      +m0 = Nat.mod(x0, R)
      +r = LS.pcs(R, xt, d0)
      +q = CA.cc(r)
      +hAE = L.subst(Nat, z => {Nat.is_le(A, z) == True{} : Bool}, A, Nat.mul(R, E), PS.at_r(one, R, hR, z => {A == Nat.mul(z, E) : Nat}, sy(Nat.mul(WD.sc(17n, one), E), A, PW.scsc(17n, 4n, one, h1))), N.le_refl(A))
      +hd0 = CA.div_lt(one, h1, R, hR, x0, E, N.lt_le_trans(x0, A, Nat.mul(R, E), NL.below_head(x0, xt, A, hx), hAE))
      +hb = pcs_below(one, h1, R, hR, xt, d0, A, E, NL.below_tail(x0, xt, A, hx), hd0, hAE)
      +hlb = L.and_left(FV.below(CA.cl(r), Nat.add(R, E)), Nat.is_lt(q, E), hb)
      +hq = L.and_right(FV.below(CA.cl(r), Nat.add(R, E)), Nat.is_lt(q, E), hb)
      +h19 = N.lt_le_trans(Nat.mul(q, 19n), Nat.mul(E, 19n), S9, PS.mul_lt_r(q, E, 19n, {==}, hq), e19(one, h1))
      +hhead = N.lt_le_trans(Nat.add(m0, Nat.mul(q, 19n)), Nat.add(R, S9), B, NL.lt_add2(m0, Nat.mul(q, 19n), R, S9, CA.mod_lt(one, h1, R, hR, x0), h19), r9(one, R, hR))
      +lE = N.le_trans(Nat.add(R, E), Nat.add(R, S9), B, N.le_add_left(E, S9, R, PW.le_sc(5n, 4n, one)), r9(one, R, hR))
      +out = NL.below_con(Nat.add(m0, Nat.mul(q, 19n)), CA.cl(r), B, hhead, NL.below_mono(CA.cl(r), Nat.add(R, E), B, lE, hlb))
      L.subst(List<&2, Nat>, z => {FV.below(z, B) == True{} : Bool}, Con{Nat.add(m0, Nat.mul(q, 19n)), CA.cl(r)}, LS.pc_fin(m0, r), Equal.sym(List<&2, Nat>, LS.pc_fin(m0, r), Con{Nat.add(m0, Nat.mul(q, 19n)), CA.cl(r)}, pcfin_eq(m0, r)), out)
