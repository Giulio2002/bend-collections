import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./num.bend as M
import ./limbs.bend as LM
import ./poly.bend as PL
import ./fold.bend as FD
import ./reduce.bend as RD
import ./consts.bend as K
import ./fieldops.bend as FO
import ./cong.bend as G

# freeze (the canonical representative, below p) of a tight element: csub
# adds 2^256 - p = 2^255 + 19 and keeps the sum when it carries out (x >= p,
# the sum is x - p), else keeps x; twice suffices since 2^256 < 3 p.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- constants ----

def comp_p_shape() -> {F.comp_p() == Con{19, K.rep(30n, 0, Con{128, Nil{}})} : List<&2, U32>}:
  {==}

def comp_p_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {K.valo(one, F.comp_p()) == Nat.add(1n+pp, 38n) : Nat}:
  +P = {1n+pp : Nat}
  +R = K.rep(30n, 0, Con{128, Nil{}})
  %Equal.sym(List<&2, U32>, F.comp_p(), Con{19, R}, comp_p_shape()) : {K.valo(one, _) == Nat.add(P, 38n) : Nat}
  +e1 = K.run0(one, 30n, Con{128, Nil{}})
  +e2 = L.subst(Nat, o => {K.valo(o, Con{128, Nil{}}) == WD.sc(7n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +e3 = Equal.trans(Nat, K.valo(one, R), LM.shn(30n, K.valo(one, Con{128, Nil{}})), LM.shn(30n, WD.sc(7n, one)), e1, Equal.cong(Nat, Nat, t => LM.shn(30n, t), K.valo(one, Con{128, Nil{}}), WD.sc(7n, one), e2))
  +e4 = M.cong_add(Nat.mul(one, v(19)), 19n, C.shift(8n, K.valo(one, R)), WD.sc(255n, one), K.one_k(one, h1, v(19)), M.cong_sc(8n, K.valo(one, R), LM.shn(30n, WD.sc(7n, one)), e3))
  +e5 = M.cong_r(19n, WD.sc(255n, one), Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), WD.sc(255n, one), hP))
  Equal.trans(Nat, Nat.add(Nat.mul(one, v(19)), C.shift(8n, K.valo(one, R))), Nat.add(19n, WD.sc(255n, one)), Nat.add(P, 38n), e4, Equal.trans(Nat, Nat.add(19n, WD.sc(255n, one)), Nat.add(19n, Nat.add(P, 19n)), Nat.add(P, 38n), e5, NA.add_swap(19n, P, 19n)))

def comp_p_okb() -> {LM.okb(32n, F.comp_p(), 128n) == True{} : Bool}:
  {==}

# 2^256 == 2 p + 38
def t_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {LM.shn(32n, one) == Nat.add(Nat.add(1n+pp, 1n+pp), 38n) : Nat}:
  +P = {1n+pp : Nat}
  +X = WD.sc(255n, one)
  +e1 = Equal.sym(Nat, Nat.add(X, X), WD.sc(256n, one), M.sc_dbl(255n, one))
  +e2 = M.cong_add(X, Nat.add(P, 19n), X, Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), X, hP), Equal.sym(Nat, Nat.add(P, 19n), X, hP))
  Equal.trans(Nat, WD.sc(256n, one), Nat.add(X, X), Nat.add(Nat.add(P, P), 38n), e1, Equal.trans(Nat, Nat.add(X, X), Nat.add(Nat.add(P, 19n), Nat.add(P, 19n)), Nat.add(Nat.add(P, P), 38n), e2, M.add4(P, 19n, P, 19n)))

# 38 <= p
def p38(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.is_le(38n, 1n+pp) == True{} : Bool}:
  +P = {1n+pp : Nat}
  +a = L.subst(Nat, o => {Nat.is_le(64n, WD.sc(6n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +b = N.le_trans(64n, WD.sc(6n, one), WD.sc(255n, one), a, M.sc_mono(249n, 6n, one))
  +c = L.subst(Nat, z => {Nat.is_le(64n, z) == True{} : Bool}, WD.sc(255n, one), Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), WD.sc(255n, one), hP), b)
  +c2 = L.subst(Nat, z => {Nat.is_le(64n, z) == True{} : Bool}, Nat.add(P, 19n), Nat.add(19n, P), NA.add_comm(P, 19n), c)
  +d = L.subst(Nat, z => {Nat.is_le(z, Nat.add(19n, P)) == True{} : Bool}, 64n, Nat.add(19n, 45n), {==}, c2)
  +e = L.subst(Bool, z => {z == True{} : Bool}, Nat.is_le(Nat.add(19n, 45n), Nat.add(19n, P)), Nat.is_le(45n, P), NR.le_add_cancel(19n, 45n, P), d)
  N.le_trans(38n, 45n, P, {==}, e)

# ---- one conditional subtraction, with the constant as a parameter ----

def csg(+x: List<&2, U32>, +cp: List<&2, U32>) -> List<&2, U32>:
  F.csub_fin(F.carry(F.addl(x, cp), 0), x)

def cs_eta(+r: F.Cr, +x: List<&2, U32>) -> {F.csub_fin(r, x) == F.select(LM.cc(r), x, LM.cl(r)) : List<&2, U32>}:
  match r:
    case F.Cr{a, c}:
      {==}

def ad_okb(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}) -> {LM.okb(32n, F.addl(x, cp), WD.sc(28n, one)) == True{} : Bool}:
  +e = PL.addl_okb(one, h1, 32n, x, cp, 255n, 128n, hx, LM.okb_lea(32n, cp, 128n, hk), PL.okb_len_le(32n, cp, 128n, hk), FO.lt32_small(one, h1, Nat.add(255n, 128n), {==}))
  PL.okb_mono(32n, F.addl(x, cp), Nat.add(255n, 128n), WD.sc(28n, one), FO.le_small(one, h1, Nat.add(255n, 128n), {==}), e)

# value(s) + 2^256 c == value(x) + (p + 38)
def cs_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), LM.shn(32n, v(LM.cc(F.carry(F.addl(x, cp), 0))))) == Nat.add(FS.value(x), Nat.add(1n+pp, 38n)) : Nat}:
  +ys = F.addl(x, cp)
  +e1 = FD.cr_val(one, h1, ys, ad_okb(one, h1, x, cp, hx, hk))
  +e2 = PL.addl_val(one, h1, x, cp, 255n, 128n, LM.okb_lea(32n, x, 255n, hx), LM.okb_lea(32n, cp, 128n, hk), FO.lt32_small(one, h1, Nat.add(255n, 128n), {==}))
  +e3 = Equal.trans(Nat, FS.value(cp), K.valo(one, cp), Nat.add(1n+pp, 38n), Equal.sym(Nat, K.valo(one, cp), FS.value(cp), K.valo_value(one, h1, cp)), hv)
  Equal.trans(Nat, Nat.add(FS.value(LM.cl(F.carry(ys, 0))), LM.shn(32n, v(LM.cc(F.carry(ys, 0))))), FS.value(ys), Nat.add(FS.value(x), Nat.add(1n+pp, 38n)), e1, Equal.trans(Nat, FS.value(ys), Nat.add(FS.value(x), FS.value(cp)), Nat.add(FS.value(x), Nat.add(1n+pp, 38n)), e2, M.cong_r(FS.value(x), FS.value(cp), Nat.add(1n+pp, 38n), e3)))

# case c == 0 (no carry out): x < p, the result is x
def z_case(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == True{} : Bool}) -> {Nat.is_lt(FS.value(x), 1n+pp) == True{} : Bool}:
  +P = {1n+pp : Nat}
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +c0 = U.lt_one_zero(c, L.subst(Nat, o => {Nat.is_lt(c, o) == True{} : Bool}, one, 1n, h1, hc))
  +ev = cs_val(one, h1, pp, x, cp, hx, hk, hv)
  +ev0 = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), Nat.add(P, 38n)) : Nat}, c, 0n, c0, ev)
  +ev1 = Equal.trans(Nat, vs, Nat.add(vs, 0n), Nat.add(FS.value(x), Nat.add(P, 38n)), Equal.sym(Nat, Nat.add(vs, 0n), vs, N.add_zero(vs)), ev0)
  +lt = RD.val_lt(one, h1, 32n, LM.cl(r), FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))
  +lt2 = L.subst(Nat, z => {Nat.is_lt(vs, z) == True{} : Bool}, LM.shn(32n, one), Nat.add(Nat.add(P, P), 38n), t_val(one, h1, pp, hP), lt)
  +lt3 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(Nat.add(P, P), 38n)) == True{} : Bool}, vs, Nat.add(FS.value(x), Nat.add(P, 38n)), ev1, lt2)
  +lt4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(FS.value(x), Nat.add(P, 38n)), z) == True{} : Bool}, Nat.add(Nat.add(P, P), 38n), Nat.add(P, Nat.add(P, 38n)), NA.add_assoc(P, P, 38n), lt3)
  RD.lt_cancel_r(FS.value(x), P, Nat.add(P, 38n), lt4)

# case c >= 1: c == 1 and value(s) + p == value(x)
def o_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {v(LM.cc(F.carry(F.addl(x, cp), 0))) == one : Nat}:
  +P = {1n+pp : Nat}
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +T = LM.shn(32n, one)
  +ev = cs_val(one, h1, pp, x, cp, hx, hk, hv)
  +a = N.le_trans(LM.shn(32n, c), Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), Nat.add(P, 38n)), PL.le_add_l(vs, LM.shn(32n, c)), N.eq_le(Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), Nat.add(P, 38n)), ev))
  +tv = t_val(one, h1, pp, hP)
  +k1 = L.subst(Nat, z => {Nat.is_le(Nat.add(P, 38n), z) == True{} : Bool}, Nat.add(Nat.add(P, P), 38n), T, Equal.sym(Nat, T, Nat.add(Nat.add(P, P), 38n), tv), M.le_add_r(P, Nat.add(P, P), 38n, N.le_add_right(P, P)))
  +b = N.lt_le_trans(Nat.add(FS.value(x), Nat.add(P, 38n)), Nat.add(T, Nat.add(P, 38n)), Nat.add(T, T), N.lt_add_r2(FS.value(x), T, Nat.add(P, 38n), RD.val_lt(one, h1, 32n, x, hx)), N.le_add_left(Nat.add(P, 38n), T, T, k1))
  +d = N.le_lt_trans(LM.shn(32n, c), Nat.add(FS.value(x), Nat.add(P, 38n)), Nat.add(T, T), a, b)
  +d2 = L.subst(Nat, z => {Nat.is_lt(LM.shn(32n, c), z) == True{} : Bool}, Nat.add(T, T), LM.shn(32n, Nat.add(one, one)), M.sc_add(256n, one, one), d)
  +c2 = RD.shn_lt_cancel(c, Nat.add(one, one), d2)
  +c2b = L.subst(Nat, o => {Nat.is_lt(c, Nat.add(o, o)) == True{} : Bool}, one, 1n, h1, c2)
  +cle = L.subst(Nat, o => {Nat.is_le(c, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le(c, 1n, c2b))
  N.le_antisym(c, one, cle, N.not_lt_le(c, one, hc))

def o_case(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), 1n+pp) == FS.value(x) : Nat}:
  +P = {1n+pp : Nat}
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +ev = cs_val(one, h1, pp, x, cp, hx, hk, hv)
  +ev1 = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), Nat.add(P, 38n)) : Nat}, c, one, o_c(one, h1, pp, hP, x, cp, hx, hk, hv, hc), ev)
  +ev2 = L.subst(Nat, z => {Nat.add(vs, z) == Nat.add(FS.value(x), Nat.add(P, 38n)) : Nat}, LM.shn(32n, one), Nat.add(Nat.add(P, P), 38n), t_val(one, h1, pp, hP), ev1)
  +ev3 = Equal.trans(Nat, Nat.add(Nat.add(vs, P), Nat.add(P, 38n)), Nat.add(vs, Nat.add(P, Nat.add(P, 38n))), Nat.add(FS.value(x), Nat.add(P, 38n)), NA.add_assoc(vs, P, Nat.add(P, 38n)), Equal.trans(Nat, Nat.add(vs, Nat.add(P, Nat.add(P, 38n))), Nat.add(vs, Nat.add(Nat.add(P, P), 38n)), Nat.add(FS.value(x), Nat.add(P, 38n)), M.cong_r(vs, Nat.add(P, Nat.add(P, 38n)), Nat.add(Nat.add(P, P), 38n), Equal.sym(Nat, Nat.add(Nat.add(P, P), 38n), Nat.add(P, Nat.add(P, 38n)), NA.add_assoc(P, P, 38n))), ev2))
  G.cancel_r(Nat.add(vs, P), FS.value(x), Nat.add(P, 38n), ev3)

# csub gives x (c == 0) or its limbs s (c == 1)
def cs_zero(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == True{} : Bool}) -> {csg(x, cp) == x : List<&2, U32>}:
  +r = F.carry(F.addl(x, cp), 0)
  +c0 = U.lt_one_zero(v(LM.cc(r)), L.subst(Nat, o => {Nat.is_lt(v(LM.cc(r)), o) == True{} : Bool}, one, 1n, h1, hc))
  +cz = U.injective(LM.cc(r), 0, c0)
  %Equal.sym(List<&2, U32>, F.csub_fin(r, x), F.select(LM.cc(r), x, LM.cl(r)), cs_eta(r, x)) : {_ == x : List<&2, U32>}
  %Equal.cong(U32, List<&2, U32>, z => F.select(z, x, LM.cl(r)), 0, LM.cc(r), Equal.sym(U32, LM.cc(r), 0, cz)) : {_ == x : List<&2, U32>}
  FO.select0(one, h1, 32n, x, LM.cl(r), hx, FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))

def cs_one(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {csg(x, cp) == LM.cl(F.carry(F.addl(x, cp), 0)) : List<&2, U32>}:
  +r = F.carry(F.addl(x, cp), 0)
  +c1 = Equal.trans(Nat, v(LM.cc(r)), one, 1n, o_c(one, h1, pp, hP, x, cp, hx, hk, hv, hc), h1)
  +co = U.injective(LM.cc(r), 1, c1)
  %Equal.sym(List<&2, U32>, F.csub_fin(r, x), F.select(LM.cc(r), x, LM.cl(r)), cs_eta(r, x)) : {_ == LM.cl(r) : List<&2, U32>}
  %Equal.cong(U32, List<&2, U32>, z => F.select(z, x, LM.cl(r)), 1, LM.cc(r), Equal.sym(U32, LM.cc(r), 1, co)) : {_ == LM.cl(r) : List<&2, U32>}
  FO.select1(one, h1, 32n, x, LM.cl(r), hx, FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))
