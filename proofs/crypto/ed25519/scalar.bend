import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/poly.bend as PL
import ../curve25519/fold.bend as FD
import ../curve25519/reduce.bend as RD
import ../curve25519/consts.bend as K
import ../curve25519/fieldops.bend as FO
import ../curve25519/cong.bend as G

# Scalars mod a modulus M = 1 + mm below 2^255 (L for Ed25519) as tight
# 32-limb values: the conditional subtraction (adding 2^256 - M carries out
# exactly when x >= M), addm, the double-and-add loop mac, reduce and
# mul_add of src/crypto/ed25519/scalar.bend. The constant cp = 2^256 - M is
# a parameter, related to M through the symbolic one.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def T(+one: Nat) -> Nat:
  LM.shn(32n, one)

# ---- x + cp, carried ----

def ad_okb(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}) -> {LM.okb(32n, F.addl(x, cp), WD.sc(28n, one)) == True{} : Bool}:
  FO.addl_okb(one, h1, x, cp, hx, hk)

def cvx(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), LM.shn(32n, v(LM.cc(F.carry(F.addl(x, cp), 0))))) == Nat.add(FS.value(x), FS.value(cp)) : Nat}:
  +ys = F.addl(x, cp)
  Equal.trans(Nat, Nat.add(FS.value(LM.cl(F.carry(ys, 0))), LM.shn(32n, v(LM.cc(F.carry(ys, 0))))), FS.value(ys), Nat.add(FS.value(x), FS.value(cp)), FD.cr_val(one, h1, ys, ad_okb(one, h1, x, cp, hx, hk)), PL.addl_val(one, h1, x, cp, 255n, 255n, LM.okb_lea(32n, x, 255n, hx), LM.okb_lea(32n, cp, 255n, hk), FO.lt32_small(one, h1, Nat.add(255n, 255n), {==})))

def cp_val(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +cp: List<&2, U32>, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}) -> {Nat.add(FS.value(cp), 1n+mm) == T(one) : Nat}:
  Equal.trans(Nat, Nat.add(FS.value(cp), 1n+mm), Nat.add(K.valo(one, cp), 1n+mm), T(one), M.cong_l(FS.value(cp), K.valo(one, cp), 1n+mm, Equal.sym(Nat, K.valo(one, cp), FS.value(cp), K.valo_value(one, h1, cp))), hv)

# case c < 1: x < M
def mz(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == True{} : Bool}) -> {Nat.is_lt(FS.value(x), 1n+mm) == True{} : Bool}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +c0 = U.lt_one_zero(c, L.subst(Nat, o => {Nat.is_lt(c, o) == True{} : Bool}, one, 1n, h1, hc))
  +ev = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), VC) : Nat}, c, 0n, c0, cvx(one, h1, mm, x, cp, hx, hk))
  +ev1 = Equal.trans(Nat, vs, Nat.add(vs, 0n), Nat.add(FS.value(x), VC), Equal.sym(Nat, Nat.add(vs, 0n), vs, N.add_zero(vs)), ev)
  +lt = RD.val_lt(one, h1, 32n, LM.cl(r), FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))
  +lt2 = L.subst(Nat, z => {Nat.is_lt(vs, z) == True{} : Bool}, T(one), Nat.add(VC, 1n+mm), Equal.sym(Nat, Nat.add(VC, 1n+mm), T(one), cp_val(one, h1, mm, cp, hv)), lt)
  +lt3 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(VC, 1n+mm)) == True{} : Bool}, vs, Nat.add(FS.value(x), VC), ev1, lt2)
  +lt4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(FS.value(x), VC), z) == True{} : Bool}, Nat.add(VC, 1n+mm), Nat.add(1n+mm, VC), NA.add_comm(VC, 1n+mm), lt3)
  RD.lt_cancel_r(FS.value(x), 1n+mm, VC, lt4)

# case c >= 1 (x < 2^256): c == 1
def mo_c(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {v(LM.cc(F.carry(F.addl(x, cp), 0))) == one : Nat}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +TT = T(one)
  +ev = cvx(one, h1, mm, x, cp, hx, hk)
  +a = N.le_trans(LM.shn(32n, c), Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), VC), PL.le_add_l(vs, LM.shn(32n, c)), N.eq_le(Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), VC), ev))
  +vct = L.subst(Nat, z => {Nat.is_le(VC, z) == True{} : Bool}, Nat.add(VC, 1n+mm), TT, cp_val(one, h1, mm, cp, hv), N.le_add_right(VC, 1n+mm))
  +b = N.lt_le_trans(Nat.add(FS.value(x), VC), Nat.add(TT, VC), Nat.add(TT, TT), N.lt_add_r2(FS.value(x), TT, VC, RD.val_lt(one, h1, 32n, x, hx)), N.le_add_left(VC, TT, TT, vct))
  +d = N.le_lt_trans(LM.shn(32n, c), Nat.add(FS.value(x), VC), Nat.add(TT, TT), a, b)
  +d2 = L.subst(Nat, z => {Nat.is_lt(LM.shn(32n, c), z) == True{} : Bool}, Nat.add(TT, TT), LM.shn(32n, Nat.add(one, one)), M.sc_add(256n, one, one), d)
  +c2 = RD.shn_lt_cancel(c, Nat.add(one, one), d2)
  +c2b = L.subst(Nat, o => {Nat.is_lt(c, Nat.add(o, o)) == True{} : Bool}, one, 1n, h1, c2)
  +cle = L.subst(Nat, o => {Nat.is_le(c, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le(c, 1n, c2b))
  N.le_antisym(c, one, cle, N.not_lt_le(c, one, hc))

# case c >= 1: value(s) + M == value(x)
def mo(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), 1n+mm) == FS.value(x) : Nat}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +ev = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), VC) : Nat}, c, one, mo_c(one, h1, mm, x, cp, hx, hk, hv, hc), cvx(one, h1, mm, x, cp, hx, hk))
  +ev2 = L.subst(Nat, z => {Nat.add(vs, z) == Nat.add(FS.value(x), VC) : Nat}, T(one), Nat.add(VC, 1n+mm), Equal.sym(Nat, Nat.add(VC, 1n+mm), T(one), cp_val(one, h1, mm, cp, hv)), ev)
  +ev3 = Equal.trans(Nat, Nat.add(Nat.add(vs, 1n+mm), VC), Nat.add(vs, Nat.add(VC, 1n+mm)), Nat.add(FS.value(x), VC), Equal.trans(Nat, Nat.add(Nat.add(vs, 1n+mm), VC), Nat.add(vs, Nat.add(1n+mm, VC)), Nat.add(vs, Nat.add(VC, 1n+mm)), NA.add_assoc(vs, 1n+mm, VC), M.cong_r(vs, Nat.add(1n+mm, VC), Nat.add(VC, 1n+mm), NA.add_comm(1n+mm, VC))), ev2)
  G.cancel_r(Nat.add(vs, 1n+mm), FS.value(x), VC, ev3)

# ---- csub: tight, and value(x) mod M for x < 2 M ----

# x < M exactly when the carry is 0
def lt_by(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {U32.is_eq(LM.cc(F.carry(F.addl(x, cp), 0)), 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}:
  match b:
    case True{}:
      +r = F.carry(F.addl(x, cp), 0)
      +c0 = U.lt_one_zero(v(LM.cc(r)), L.subst(Nat, o => {Nat.is_lt(v(LM.cc(r)), o) == True{} : Bool}, one, 1n, h1, hb))
      +cz = U.injective(LM.cc(r), 0, c0)
      %Equal.sym(U32, LM.cc(r), 0, cz) : {U32.is_eq(_, 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}
      Equal.sym(Bool, Nat.is_lt(FS.value(x), 1n+mm), True{}, mz(one, h1, mm, x, cp, hx, hk, hv, hb))
    case False{}:
      +r = F.carry(F.addl(x, cp), 0)
      +co = U.injective(LM.cc(r), 1, Equal.trans(Nat, v(LM.cc(r)), one, 1n, mo_c(one, h1, mm, x, cp, hx, hk, hv, hb), h1))
      %Equal.sym(U32, LM.cc(r), 1, co) : {U32.is_eq(_, 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}
      +e1 = mo(one, h1, mm, x, cp, hx, hk, hv, hb)
      +ge = L.subst(Nat, z => {Nat.is_le(1n+mm, z) == True{} : Bool}, Nat.add(FS.value(LM.cl(r)), 1n+mm), FS.value(x), e1, PL.le_add_l(FS.value(LM.cl(r)), 1n+mm))
      Equal.sym(Bool, Nat.is_lt(FS.value(x), 1n+mm), False{}, N.le_not_lt(FS.value(x), 1n+mm, ge))

# ---- addm ----