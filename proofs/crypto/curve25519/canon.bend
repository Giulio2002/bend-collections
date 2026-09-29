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
import ../../math/u64/u64div.bend as PD
import ./num.bend as M
import ./limbs.bend as LM
import ./poly.bend as PL
import ./fold.bend as FD
import ./reduce.bend as RD
import ./consts.bend as K
import ./fieldops.bend as FO
import ./cong.bend as G
import ./freeze.bend as FZ
import ./mulw.bend as MW

# freeze, is_zero and parity: the canonical representative is the value
# mod p; is_zero tests it is 0; parity is its low bit.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- one csub ----

def by_okb(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {LM.okb(32n, FZ.csg(x, cp), 255n) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), x, FZ.cs_zero(one, h1, x, cp, hx, hk, hb)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      hx
    case False{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), LM.cl(F.carry(F.addl(x, cp), 0)), FZ.cs_one(one, h1, pp, hP, x, cp, hx, hk, hv, hb)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      FD.cr_okb(one, h1, F.addl(x, cp), FZ.ad_okb(one, h1, x, cp, hx, hk))

def by_ceq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> G.ceq(pp, FS.value(FZ.csg(x, cp)), FS.value(x)):
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), x, FZ.cs_zero(one, h1, x, cp, hx, hk, hb)) : G.ceq(pp, FS.value(_), FS.value(x))
      G.c_refl(pp, FS.value(x))
    case False{}:
      +s = LM.cl(F.carry(F.addl(x, cp), 0))
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), s, FZ.cs_one(one, h1, pp, hP, x, cp, hx, hk, hv, hb)) : G.ceq(pp, FS.value(_), FS.value(x))
      +e1 = FZ.o_case(one, h1, pp, hP, x, cp, hx, hk, hv, hb)
      +e2 = Equal.trans(Nat, Nat.add(Nat.mul(1n, 1n+pp), FS.value(s)), Nat.add(1n+pp, FS.value(s)), FS.value(x), M.cong_l(Nat.mul(1n, 1n+pp), 1n+pp, FS.value(s), AR.one_mul(1n+pp)), Equal.trans(Nat, Nat.add(1n+pp, FS.value(s)), Nat.add(FS.value(s), 1n+pp), FS.value(x), NA.add_comm(1n+pp, FS.value(s)), e1))
      +e3 = NR.absorb(pp, 1n, FS.value(s))
      G.c_sym(pp, FS.value(x), FS.value(s), G.c_trans(pp, FS.value(x), Nat.add(Nat.mul(1n, 1n+pp), FS.value(s)), FS.value(s), G.c_eq(pp, FS.value(x), Nat.add(Nat.mul(1n, 1n+pp), FS.value(s)), Equal.sym(Nat, Nat.add(Nat.mul(1n, 1n+pp), FS.value(s)), FS.value(x), e2)), e3))

def by_lt(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 128n) == True{} : Bool}, +hv: {K.valo(one, cp) == Nat.add(1n+pp, 38n) : Nat}, +bB: Nat, +q: Nat, +hxB: {Nat.is_lt(FS.value(x), Nat.add(1n+pp, bB)) == True{} : Bool}, +hPQ: {Nat.is_le(1n+pp, q) == True{} : Bool}, +hBQ: {Nat.is_le(bB, q) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {Nat.is_lt(FS.value(FZ.csg(x, cp)), q) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), x, FZ.cs_zero(one, h1, x, cp, hx, hk, hb)) : {Nat.is_lt(FS.value(_), q) == True{} : Bool}
      N.lt_le_trans(FS.value(x), 1n+pp, q, FZ.z_case(one, h1, pp, hP, x, cp, hx, hk, hv, hb), hPQ)
    case False{}:
      +s = LM.cl(F.carry(F.addl(x, cp), 0))
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), s, FZ.cs_one(one, h1, pp, hP, x, cp, hx, hk, hv, hb)) : {Nat.is_lt(FS.value(_), q) == True{} : Bool}
      +e1 = FZ.o_case(one, h1, pp, hP, x, cp, hx, hk, hv, hb)
      +l1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(1n+pp, bB)) == True{} : Bool}, FS.value(x), Nat.add(FS.value(s), 1n+pp), Equal.sym(Nat, Nat.add(FS.value(s), 1n+pp), FS.value(x), e1), hxB)
      +l2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(FS.value(s), 1n+pp), z) == True{} : Bool}, Nat.add(1n+pp, bB), Nat.add(bB, 1n+pp), NA.add_comm(1n+pp, bB), l1)
      N.lt_le_trans(FS.value(s), bB, q, RD.lt_cancel_r(FS.value(s), bB, 1n+pp, l2), hBQ)

def cs_c(+one: Nat, +x: List<&2, U32>, +cp: List<&2, U32>) -> Nat:
  v(LM.cc(F.carry(F.addl(x, cp), 0)))

# ---- freeze = csub(csub(x)) with 2^256 - p ----

def csub_okb(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {LM.okb(32n, F.csub(x), 255n) == True{} : Bool}:
  by_okb(one, h1, pp, hP, x, F.comp_p(), hx, FZ.comp_p_okb(), FZ.comp_p_val(one, h1, pp, hP), Nat.is_lt(cs_c(one, x, F.comp_p()), one), {==})

def csub_ceq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.csub(x)), FS.value(x)):
  by_ceq(one, h1, pp, hP, x, F.comp_p(), hx, FZ.comp_p_okb(), FZ.comp_p_val(one, h1, pp, hP), Nat.is_lt(cs_c(one, x, F.comp_p()), one), {==})

def csub_lt(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +bB: Nat, +q: Nat, +hxB: {Nat.is_lt(FS.value(x), Nat.add(1n+pp, bB)) == True{} : Bool}, +hPQ: {Nat.is_le(1n+pp, q) == True{} : Bool}, +hBQ: {Nat.is_le(bB, q) == True{} : Bool}) -> {Nat.is_lt(FS.value(F.csub(x)), q) == True{} : Bool}:
  by_lt(one, h1, pp, hP, x, F.comp_p(), hx, FZ.comp_p_okb(), FZ.comp_p_val(one, h1, pp, hP), bB, q, hxB, hPQ, hBQ, Nat.is_lt(cs_c(one, x, F.comp_p()), one), {==})

def freeze_okb(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {LM.okb(32n, F.freeze(x), 255n) == True{} : Bool}:
  csub_okb(one, h1, pp, hP, F.csub(x), csub_okb(one, h1, pp, hP, x, hx))

def freeze_ceq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.freeze(x)), FS.value(x)):
  G.c_trans(pp, FS.value(F.csub(F.csub(x))), FS.value(F.csub(x)), FS.value(x), csub_ceq(one, h1, pp, hP, F.csub(x), csub_okb(one, h1, pp, hP, x, hx)), csub_ceq(one, h1, pp, hP, x, hx))

def freeze_lt(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {Nat.is_lt(FS.value(F.freeze(x)), 1n+pp) == True{} : Bool}:
  +P = {1n+pp : Nat}
  +t1 = RD.val_lt(one, h1, 32n, x, hx)
  +t2 = L.subst(Nat, z => {Nat.is_lt(FS.value(x), z) == True{} : Bool}, LM.shn(32n, one), Nat.add(P, Nat.add(P, 38n)), Equal.trans(Nat, LM.shn(32n, one), Nat.add(Nat.add(P, P), 38n), Nat.add(P, Nat.add(P, 38n)), FZ.t_val(one, h1, pp, hP), NA.add_assoc(P, P, 38n)), t1)
  +y1 = csub_lt(one, h1, pp, hP, x, hx, Nat.add(P, 38n), Nat.add(P, 38n), t2, N.le_add_right(P, 38n), N.le_refl(Nat.add(P, 38n)))
  csub_lt(one, h1, pp, hP, F.csub(x), csub_okb(one, h1, pp, hP, x, hx), 38n, P, y1, N.le_refl(P), FZ.p38(one, h1, pp, hP))

# value(freeze(x)) == value(x) mod p
def freeze_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {FS.value(F.freeze(x)) == Nat.mod(FS.value(x), 1n+pp) : Nat}:
  +r = FS.value(F.freeze(x))
  +e1 = Equal.sym(Nat, Nat.mod(r, 1n+pp), r, NR.mod_of(0n, pp, r, freeze_lt(one, h1, pp, hP, x, hx)))
  Equal.trans(Nat, r, Nat.mod(r, 1n+pp), Nat.mod(FS.value(x), 1n+pp), e1, freeze_ceq(one, h1, pp, hP, x, hx))

# ---- is_zero ----

def sumv(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      Nat.add(U32.to_nat(x), sumv(xt))

def sum_v(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +acc: U32, +e: {LM.okb(n, xs, 255n) == True{} : Bool}, +ha: {Nat.is_lt(Nat.add(v(acc), PL.cbn(n, WD.sc(8n, one))), WD.sc(32n, one)) == True{} : Bool}) -> {v(F.sum_all(xs, acc)) == Nat.add(v(acc), sumv(xs)) : Nat}:
  match n xs:
    case 0n Nil{}:
      Equal.sym(Nat, Nat.add(v(acc), 0n), v(acc), N.add_zero(v(acc)))
    case 0n Con{y, yt}:
      Empty.absurd({v(F.sum_all(Con{y, yt}, acc)) == Nat.add(v(acc), sumv(Con{y, yt})) : Nat}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({v(acc) == Nat.add(v(acc), 0n) : Nat}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      +hy = N.le_trans(v(y), 255n, WD.sc(8n, one), LM.okb_head(m, y, yt, 255n, e), FD.le255(one, h1, 0n))
      +b1 = N.le_lt_trans(Nat.add(v(acc), v(y)), Nat.add(v(acc), Nat.add(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one)))), WD.sc(32n, one), N.le_add_left(v(y), Nat.add(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one))), v(acc), N.le_trans(v(y), WD.sc(8n, one), Nat.add(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one))), hy, N.le_add_right(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one))))), ha)
      +ea = LM.add_v(one, h1, acc, y, b1)
      +b2a = M.le_add_r(Nat.add(v(acc), v(y)), Nat.add(v(acc), WD.sc(8n, one)), PL.cbn(m, WD.sc(8n, one)), N.le_add_left(v(y), WD.sc(8n, one), v(acc), hy))
      +b2b = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(v(acc), v(y)), PL.cbn(m, WD.sc(8n, one))), z) == True{} : Bool}, Nat.add(Nat.add(v(acc), WD.sc(8n, one)), PL.cbn(m, WD.sc(8n, one))), Nat.add(v(acc), Nat.add(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one)))), NA.add_assoc(v(acc), WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one))), b2a)
      +b2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(z, PL.cbn(m, WD.sc(8n, one))), WD.sc(32n, one)) == True{} : Bool}, Nat.add(v(acc), v(y)), v(U32.add(acc, y)), Equal.sym(Nat, v(U32.add(acc, y)), Nat.add(v(acc), v(y)), ea), N.le_lt_trans(Nat.add(Nat.add(v(acc), v(y)), PL.cbn(m, WD.sc(8n, one))), Nat.add(v(acc), Nat.add(WD.sc(8n, one), PL.cbn(m, WD.sc(8n, one)))), WD.sc(32n, one), b2b, ha))
      +ih = sum_v(one, h1, m, yt, U32.add(acc, y), LM.okb_tail(m, y, yt, 255n, e), b2)
      Equal.trans(Nat, v(F.sum_all(yt, U32.add(acc, y))), Nat.add(v(U32.add(acc, y)), sumv(yt)), Nat.add(v(acc), Nat.add(v(y), sumv(yt))), ih, Equal.trans(Nat, Nat.add(v(U32.add(acc, y)), sumv(yt)), Nat.add(Nat.add(v(acc), v(y)), sumv(yt)), Nat.add(v(acc), Nat.add(v(y), sumv(yt))), M.cong_l(v(U32.add(acc, y)), Nat.add(v(acc), v(y)), sumv(yt), ea), NA.add_assoc(v(acc), v(y), sumv(yt))))

def iz_add(+a: Nat, +b: Nat) -> {Nat.is_eq(Nat.add(a, b), 0n) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 0n)) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      {==}

def iz_dbl(+x: Nat) -> {Nat.is_eq(Nat.double(x), 0n) == Nat.is_eq(x, 0n) : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      {==}

def iz_sc(+k: Nat, +x: Nat) -> {Nat.is_eq(WD.sc(k, x), 0n) == Nat.is_eq(x, 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.trans(Bool, Nat.is_eq(Nat.double(WD.sc(q, x)), 0n), Nat.is_eq(WD.sc(q, x), 0n), Nat.is_eq(x, 0n), iz_dbl(WD.sc(q, x)), iz_sc(q, x))

def iz_sum(+xs: List<&2, U32>) -> {Nat.is_eq(sumv(xs), 0n) == Nat.is_eq(FS.value(xs), 0n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      +e1 = iz_add(v(y), sumv(yt))
      +e2 = iz_add(v(y), C.shift(8n, FS.value(yt)))
      +e3 = Equal.trans(Bool, Nat.is_eq(C.shift(8n, FS.value(yt)), 0n), Nat.is_eq(FS.value(yt), 0n), Nat.is_eq(sumv(yt), 0n), iz_sc(8n, FS.value(yt)), Equal.sym(Bool, Nat.is_eq(sumv(yt), 0n), Nat.is_eq(FS.value(yt), 0n), iz_sum(yt)))
      Equal.trans(Bool, Nat.is_eq(Nat.add(v(y), sumv(yt)), 0n), Bool.and(Nat.is_eq(v(y), 0n), Nat.is_eq(sumv(yt), 0n)), Nat.is_eq(Nat.add(v(y), C.shift(8n, FS.value(yt))), 0n), e1, Equal.trans(Bool, Bool.and(Nat.is_eq(v(y), 0n), Nat.is_eq(sumv(yt), 0n)), Bool.and(Nat.is_eq(v(y), 0n), Nat.is_eq(C.shift(8n, FS.value(yt)), 0n)), Nat.is_eq(Nat.add(v(y), C.shift(8n, FS.value(yt))), 0n), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(v(y), 0n), z), Nat.is_eq(sumv(yt), 0n), Nat.is_eq(C.shift(8n, FS.value(yt)), 0n), Equal.sym(Bool, Nat.is_eq(C.shift(8n, FS.value(yt)), 0n), Nat.is_eq(sumv(yt), 0n), e3)), Equal.sym(Bool, Nat.is_eq(Nat.add(v(y), C.shift(8n, FS.value(yt))), 0n), Bool.and(Nat.is_eq(v(y), 0n), Nat.is_eq(C.shift(8n, FS.value(yt)), 0n)), e2)))

def u32_iz(+a: U32) -> {U32.is_eq(a, 0) == Nat.is_eq(v(a), 0n) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, 0), Nat.cmp(v(a), 0n), U.u32_cmp(a, 0))

def cb32_lt(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(Nat.add(v(0), PL.cbn(32n, WD.sc(8n, one))), WD.sc(32n, one)) == True{} : Bool}:
  +b = MW.cbn_pow(5n, WD.sc(8n, one))
  L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, WD.sc(5n, WD.sc(8n, one)), PL.cbn(32n, WD.sc(8n, one)), Equal.sym(Nat, PL.cbn(32n, WD.sc(8n, one)), WD.sc(5n, WD.sc(8n, one)), b), LM.sc_lt(18n, 13n, one, h1))

def is_zero_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {F.is_zero(x) == Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), 0n) : Bool}:
  +y = F.freeze(x)
  +hy = freeze_okb(one, h1, pp, hP, x, hx)
  +e1 = u32_iz(F.sum_all(y, 0))
  +e2 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(F.sum_all(y, 0)), sumv(y), sum_v(one, h1, 32n, y, 0, hy, cb32_lt(one, h1)))
  +e3 = iz_sum(y)
  +e4 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), FS.value(y), Nat.mod(FS.value(x), 1n+pp), freeze_val(one, h1, pp, hP, x, hx))
  Equal.trans(Bool, U32.is_eq(F.sum_all(y, 0), 0), Nat.is_eq(v(F.sum_all(y, 0)), 0n), Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), 0n), e1, Equal.trans(Bool, Nat.is_eq(v(F.sum_all(y, 0)), 0n), Nat.is_eq(sumv(y), 0n), Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), 0n), e2, Equal.trans(Bool, Nat.is_eq(sumv(y), 0n), Nat.is_eq(FS.value(y), 0n), Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), 0n), e3, e4)))

# ---- parity ----

def and1(+one: Nat, +h1: {one == 1n : Nat}, +l: U32) -> {v(U32.and(l, 1)) == Nat.mod(v(l), 2n) : Nat}:
  +a = PD.and32(1n, l, 1, {==})
  +b = PD.and32_lt(1n, one, h1, l, 1, {==})
  +hp = PD.hp32(1n, l)
  +b2 = L.subst(Nat, o => {Nat.is_lt(v(U32.and(l, 1)), WD.sc(1n, o)) == True{} : Bool}, one, 1n, h1, b)
  +e1 = Equal.trans(Nat, v(l), Nat.add(v(U32.and(l, 1)), WD.sc(1n, hp)), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), a, Equal.trans(Nat, Nat.add(v(U32.and(l, 1)), WD.sc(1n, hp)), Nat.add(WD.sc(1n, hp), v(U32.and(l, 1))), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), NA.add_comm(v(U32.and(l, 1)), WD.sc(1n, hp)), M.cong_l(WD.sc(1n, hp), Nat.mul(hp, 2n), v(U32.and(l, 1)), Equal.trans(Nat, Nat.double(hp), Nat.mul(2n, hp), Nat.mul(hp, 2n), NA.double_mul(hp), NA.mul_comm(2n, hp)))))
  Equal.sym(Nat, Nat.mod(v(l), 2n), v(U32.and(l, 1)), Equal.trans(Nat, Nat.mod(v(l), 2n), Nat.mod(Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), 2n), v(U32.and(l, 1)), M.cong_mod(2n, v(l), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), e1), NR.mod_of(hp, 1n, v(U32.and(l, 1)), b2)))

# the value mod 2 is the low limb mod 2
def low_bit_val(+one: Nat, +h1: {one == 1n : Nat}, +ys: List<&2, U32>, +e: {LM.okb(32n, ys, 255n) == True{} : Bool}) -> {v(F.low_bit(ys)) == Nat.mod(FS.value(ys), 2n) : Nat}:
  match ys:
    case Nil{}:
      Empty.absurd({0n == Nat.mod(0n, 2n) : Nat}, L.false_true(e))
    case Con{+l, +t}:
      +V = FS.value(t)
      +q = WD.sc(7n, V)
      +e1 = Equal.trans(Nat, Nat.add(v(l), C.shift(8n, V)), Nat.add(C.shift(8n, V), v(l)), Nat.add(Nat.mul(q, 2n), v(l)), NA.add_comm(v(l), C.shift(8n, V)), M.cong_l(C.shift(8n, V), Nat.mul(q, 2n), v(l), Equal.trans(Nat, Nat.double(q), Nat.mul(2n, q), Nat.mul(q, 2n), NA.double_mul(q), NA.mul_comm(2n, q))))
      +e2 = Equal.trans(Nat, Nat.mod(Nat.add(v(l), C.shift(8n, V)), 2n), Nat.mod(Nat.add(Nat.mul(q, 2n), v(l)), 2n), Nat.mod(v(l), 2n), M.cong_mod(2n, Nat.add(v(l), C.shift(8n, V)), Nat.add(Nat.mul(q, 2n), v(l)), e1), NR.absorb(1n, q, v(l)))
      Equal.trans(Nat, v(U32.and(l, 1)), Nat.mod(v(l), 2n), Nat.mod(Nat.add(v(l), C.shift(8n, V)), 2n), and1(one, h1, l), Equal.sym(Nat, Nat.mod(Nat.add(v(l), C.shift(8n, V)), 2n), Nat.mod(v(l), 2n), e2))

def parity_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {v(F.parity(x)) == Nat.mod(Nat.mod(FS.value(x), 1n+pp), 2n) : Nat}:
  +y = F.freeze(x)
  Equal.trans(Nat, v(F.low_bit(y)), Nat.mod(FS.value(y), 2n), Nat.mod(Nat.mod(FS.value(x), 1n+pp), 2n), low_bit_val(one, h1, y, freeze_okb(one, h1, pp, hP, x, hx)), M.cong_mod(2n, FS.value(y), Nat.mod(FS.value(x), 1n+pp), freeze_val(one, h1, pp, hP, x, hx)))
