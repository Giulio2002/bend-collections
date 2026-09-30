import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
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

# The carry pass of src/crypto/curve25519/limbs.bend (carry0, then the
# carry out c of limb 14 re-enters as 19 c, since 2^255 == 19 mod p) on 15
# limbs: the value is kept mod p = 1 + pp (hP: p + 19 == 2^255), and limbs
# below 2^47 come out below 2^19 (limbs 2.. below R, limb 0 below R, limb 1
# below R + 2^18 + R = 2^19: the carry out is below 2^31, so 19 c + R <
# R (2^18 + R)).

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def ln(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      1n+ln(xt)

def shl_sh(+xs: List<&2, Nat>, +x: Nat) -> {CA.shl(xs, x) == NL.sh(ln(xs), x) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      M.cong_sc(17n, CA.shl(t, x), NL.sh(ln(t), x), shl_sh(t, x))

# ---- mod p ----

# 2^255 c == 19 c (mod p)
def c19(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +c: Nat) -> G.ceq(pp, WD.sc(255n, c), Nat.mul(c, 19n)):
  +P = {1n+pp : Nat}
  +e1 = sy(Nat.mul(c, WD.sc(255n, one)), WD.sc(255n, c), AR.mul_sc1(255n, one, h1, c))
  +e2 = Equal.cong(Nat, Nat, z => Nat.mul(c, z), WD.sc(255n, one), Nat.add(P, 19n), sy(Nat.add(P, 19n), WD.sc(255n, one), hP))
  +e3 = NA.mul_add_left(c, P, 19n)
  +e = tr(WD.sc(255n, c), Nat.mul(c, WD.sc(255n, one)), Nat.add(Nat.mul(c, P), Nat.mul(c, 19n)), e1, tr(Nat.mul(c, WD.sc(255n, one)), Nat.mul(c, Nat.add(P, 19n)), Nat.add(Nat.mul(c, P), Nat.mul(c, 19n)), e2, e3))
  G.c_trans(pp, WD.sc(255n, c), Nat.add(Nat.mul(c, P), Nat.mul(c, 19n)), Nat.mul(c, 19n), G.c_eq(pp, WD.sc(255n, c), Nat.add(Nat.mul(c, P), Nat.mul(c, 19n)), e), NR.absorb(pp, c, Nat.mul(c, 19n)))

# ---- the pass ----

def cr2(+l0: Nat, +l1: Nat, +r: LS.Cr) -> {LS.cr_con(l0, LS.cr_con(l1, r)) == LS.Cr{Con{l0, Con{l1, LS.cr_limbs(r)}}, LS.cr_out(r)} : LS.Cr}:
  match r:
    case LS.Cr{a, c}:
      {==}

# value(pass_fin) == value(limbs) + 19 c
def fin_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +r0: Nat, +r1: Nat, +rs: List<&2, Nat>, +c: Nat) -> {FV.lv(LS.pass_fin(R, LS.Cr{Con{r0, Con{r1, rs}}, c})) == Nat.add(FV.lv(Con{r0, Con{r1, rs}}), Nat.mul(c, 19n)) : Nat}:
  +t = Nat.add(r0, Nat.mul(c, 19n))
  +d = Nat.div(t, R)
  +m = Nat.mod(t, R)
  +SL = C.shift(17n, FV.lv(rs))
  +e1 = M.cong_r(m, C.shift(17n, Nat.add(Nat.add(r1, d), SL)), C.shift(17n, Nat.add(d, Nat.add(r1, SL))), M.cong_sc(17n, Nat.add(Nat.add(r1, d), SL), Nat.add(d, Nat.add(r1, SL)), tr(Nat.add(Nat.add(r1, d), SL), Nat.add(r1, Nat.add(d, SL)), Nat.add(d, Nat.add(r1, SL)), NA.add_assoc(r1, d, SL), NA.add_swap(r1, d, SL))))
  +e2 = M.cong_r(m, C.shift(17n, Nat.add(d, Nat.add(r1, SL))), Nat.add(C.shift(17n, d), C.shift(17n, Nat.add(r1, SL))), sy(Nat.add(C.shift(17n, d), C.shift(17n, Nat.add(r1, SL))), C.shift(17n, Nat.add(d, Nat.add(r1, SL))), M.sc_add(17n, d, Nat.add(r1, SL))))
  +e3 = sy(Nat.add(Nat.add(m, C.shift(17n, d)), C.shift(17n, Nat.add(r1, SL))), Nat.add(m, Nat.add(C.shift(17n, d), C.shift(17n, Nat.add(r1, SL)))), NA.add_assoc(m, C.shift(17n, d), C.shift(17n, Nat.add(r1, SL))))
  +e4 = M.cong_l(Nat.add(m, C.shift(17n, d)), t, C.shift(17n, Nat.add(r1, SL)), CA.dm(one, h1, R, hR, t))
  +e5 = CA.swap3(r0, Nat.mul(c, 19n), C.shift(17n, Nat.add(r1, SL)))
  +X0 = Nat.add(m, C.shift(17n, Nat.add(Nat.add(r1, d), SL)))
  +X1 = Nat.add(m, C.shift(17n, Nat.add(d, Nat.add(r1, SL))))
  +X2 = Nat.add(m, Nat.add(C.shift(17n, d), C.shift(17n, Nat.add(r1, SL))))
  +X3 = Nat.add(Nat.add(m, C.shift(17n, d)), C.shift(17n, Nat.add(r1, SL)))
  +X4 = Nat.add(t, C.shift(17n, Nat.add(r1, SL)))
  +X5 = Nat.add(Nat.add(r0, C.shift(17n, Nat.add(r1, SL))), Nat.mul(c, 19n))
  tr(X0, X1, X5, e1, tr(X1, X2, X5, e2, tr(X2, X3, X5, e3, tr(X3, X4, X5, e4, e5))))

# pass on at least two limbs, through its carry chain
def pass_eq(+R: Nat, +x0: Nat, +x1: Nat, +rest: List<&2, Nat>) -> {LS.pass(R, Con{x0, Con{x1, rest}}) == LS.pass_fin(R, LS.Cr{LS.cr_limbs(LS.carry0(R, Con{x0, Con{x1, rest}})), LS.cr_out(LS.carry0(R, Con{x0, Con{x1, rest}}))}) : List<&2, Nat>}:
  +xs = {Con{x0, Con{x1, rest}} : List<&2, Nat>}
  Equal.cong(LS.Cr, List<&2, Nat>, z => LS.pass_fin(R, z), LS.carry0(R, xs), LS.Cr{LS.cr_limbs(LS.carry0(R, xs)), LS.cr_out(LS.carry0(R, xs))}, CA.cr_eta(LS.carry0(R, xs)))

# the limbs of carry0 on two or more limbs: two heads and the rest
def c0_limbs(+R: Nat, +x0: Nat, +x1: Nat, +rest: List<&2, Nat>) -> {LS.cr_limbs(LS.carry0(R, Con{x0, Con{x1, rest}})) == Con{Nat.mod(x0, R), Con{Nat.mod(Nat.add(x1, Nat.div(x0, R)), R), LS.cr_limbs(LS.carry(R, rest, Nat.div(Nat.add(x1, Nat.div(x0, R)), R)))}} : List<&2, Nat>}:
  +s1 = Nat.add(x1, Nat.div(x0, R))
  +r = LS.carry(R, rest, Nat.div(s1, R))
  Equal.cong(LS.Cr, List<&2, Nat>, z => LS.cr_limbs(z), LS.cr_con(Nat.mod(x0, R), LS.cr_con(Nat.mod(s1, R), r)), LS.Cr{Con{Nat.mod(x0, R), Con{Nat.mod(s1, R), LS.cr_limbs(r)}}, LS.cr_out(r)}, cr2(Nat.mod(x0, R), Nat.mod(s1, R), r))

# value(pass(xs)) == value(xs) (mod p) for 15 limbs
def pass_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +hl: {ln(xs) == 15n : Nat}) -> G.ceq(pp, FV.lv(LS.pass(R, xs)), FV.lv(xs)):
  match xs:
    case Nil{}:
      Empty.absurd(G.ceq(pp, 0n, 0n), N.zero_succ(14n, hl))
    case Con{x0, Nil{}}:
      Empty.absurd(G.ceq(pp, FV.lv(LS.pass(R, Con{x0, Nil{}})), FV.lv(Con{x0, Nil{}})), N.zero_succ(13n, N.succ_inj(0n, 14n, hl)))
    case Con{+x0, Con{+x1, +rest}}:
      +xs2 = {Con{x0, Con{x1, rest}} : List<&2, Nat>}
      +K = LS.carry0(R, xs2)
      +s1 = Nat.add(x1, Nat.div(x0, R))
      +r = LS.carry(R, rest, Nat.div(s1, R))
      +m0 = Nat.mod(x0, R)
      +m1 = Nat.mod(s1, R)
      +c = LS.cr_out(K)
      +el = c0_limbs(R, x0, x1, rest)
      +e0 = pass_eq(R, x0, x1, rest)
      +e1 = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.pass_fin(R, LS.Cr{z, c}), LS.cr_limbs(K), Con{m0, Con{m1, LS.cr_limbs(r)}}, el)
      +ep = Equal.trans(List<&2, Nat>, LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{LS.cr_limbs(K), c}), LS.pass_fin(R, LS.Cr{Con{m0, Con{m1, LS.cr_limbs(r)}}, c}), e0, e1)
      +ev = Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), LS.pass(R, xs2), LS.pass_fin(R, LS.Cr{Con{m0, Con{m1, LS.cr_limbs(r)}}, c}), ep)
      +ef = fin_val(one, h1, R, hR, m0, m1, LS.cr_limbs(r), c)
      +eK = Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), Con{m0, Con{m1, LS.cr_limbs(r)}}, LS.cr_limbs(K), Equal.sym(List<&2, Nat>, LS.cr_limbs(K), Con{m0, Con{m1, LS.cr_limbs(r)}}, el))
      +LK = FV.lv(LS.cr_limbs(K))
      +e2 = tr(FV.lv(LS.pass(R, xs2)), Nat.add(FV.lv(Con{m0, Con{m1, LS.cr_limbs(r)}}), Nat.mul(c, 19n)), Nat.add(LK, Nat.mul(c, 19n)), tr(FV.lv(LS.pass(R, xs2)), FV.lv(LS.pass_fin(R, LS.Cr{Con{m0, Con{m1, LS.cr_limbs(r)}}, c})), Nat.add(FV.lv(Con{m0, Con{m1, LS.cr_limbs(r)}}), Nat.mul(c, 19n)), ev, ef), M.cong_l(FV.lv(Con{m0, Con{m1, LS.cr_limbs(r)}}), LK, Nat.mul(c, 19n), eK))
      +ecv = CA.carry0_val(one, h1, R, hR, xs2)
      +esh = tr(CA.shl(xs2, c), NL.sh(15n, c), WD.sc(255n, c), tr(CA.shl(xs2, c), NL.sh(ln(xs2), c), NL.sh(15n, c), shl_sh(xs2, c), Equal.cong(Nat, Nat, z => NL.sh(z, c), ln(xs2), 15n, hl)), NL.sh15(c))
      +e3 = G.c_add(pp, LK, LK, Nat.mul(c, 19n), CA.shl(xs2, c), G.c_refl(pp, LK), G.c_sym(pp, CA.shl(xs2, c), Nat.mul(c, 19n), G.c_trans(pp, CA.shl(xs2, c), WD.sc(255n, c), Nat.mul(c, 19n), G.c_eq(pp, CA.shl(xs2, c), WD.sc(255n, c), esh), c19(one, h1, pp, hP, c))))
      G.c_trans(pp, FV.lv(LS.pass(R, xs2)), Nat.add(LK, Nat.mul(c, 19n)), FV.lv(xs2), G.c_eq(pp, FV.lv(LS.pass(R, xs2)), Nat.add(LK, Nat.mul(c, 19n)), e2), G.c_trans(pp, Nat.add(LK, Nat.mul(c, 19n)), Nat.add(LK, CA.shl(xs2, c)), FV.lv(xs2), e3, G.c_eq(pp, Nat.add(LK, CA.shl(xs2, c)), FV.lv(xs2), ecv)))

# ---- bounds ----

# x < y, 0 < k -> x k < y k
def mul_lt_r(+x: Nat, +y: Nat, +k: Nat, +hk: {Nat.is_lt(0n, k) == True{} : Bool}, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, k), Nat.mul(y, k)) == True{} : Bool}:
  +xk = Nat.mul(x, k)
  +a = M.le_mul2(1n+x, k, y, k, N.lt_succ_le_succ(x, y, h), N.le_refl(k))
  +b0 = N.lt_add_left(0n, k, xk, hk)
  +b1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(xk, k)) == True{} : Bool}, Nat.add(xk, 0n), xk, N.add_zero(xk), b0)
  +b2 = L.subst(Nat, z => {Nat.is_lt(xk, z) == True{} : Bool}, Nat.add(xk, k), Nat.add(k, xk), NA.add_comm(xk, k), b1)
  N.lt_le_trans(xk, Nat.add(k, xk), Nat.mul(y, k), b2, a)

# a statement about 2^17, restated about R
def at_r(+one: Nat, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, -M: Nat -> Type, pf: M(WD.sc(17n, one))) -> M(R):
  L.subst(Nat, M, WD.sc(17n, one), R, Equal.sym(Nat, R, WD.sc(17n, one), hR), pf)

# 2^47 + 2^31 <= R 2^31 (= 2^48)
def f_chain(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(WD.sc(47n, one), WD.sc(31n, one)), Nat.mul(R, WD.sc(31n, one))) == True{} : Bool}:
  +a = PW.add_le_dbl(WD.sc(47n, one), WD.sc(31n, one), 47n, one, N.le_refl(WD.sc(47n, one)), PW.le_sc(16n, 31n, one))
  +b = L.subst(Nat, z => {Nat.is_le(Nat.add(WD.sc(47n, one), WD.sc(31n, one)), z) == True{} : Bool}, WD.sc(48n, one), Nat.mul(WD.sc(17n, one), WD.sc(31n, one)), sy(Nat.mul(WD.sc(17n, one), WD.sc(31n, one)), WD.sc(48n, one), PW.scsc(17n, 31n, one, h1)), a)
  at_r(one, R, hR, z => {Nat.is_le(Nat.add(WD.sc(47n, one), WD.sc(31n, one)), Nat.mul(z, WD.sc(31n, one))) == True{} : Bool}, b)

# R 2^31 == 2^48
def f_re(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.mul(R, WD.sc(31n, one)) == WD.sc(48n, one) : Nat}:
  at_r(one, R, hR, z => {Nat.mul(z, WD.sc(31n, one)) == WD.sc(48n, one) : Nat}, PW.scsc(17n, 31n, one, h1))

# x 2^k == 2^k x for closed 2^k
def mulp(+k: Nat, +x: Nat) -> {Nat.mul(x, WD.sc(k, 1n)) == WD.sc(k, x) : Nat}:
  AR.mul_sc(k, x)