import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/typed/width.bend as WI
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/poly.bend as PL
import ../curve25519/fold.bend as FD
import ../curve25519/reduce.bend as RD
import ../curve25519/consts.bend as K
import ../curve25519/fieldops.bend as FO
import ../curve25519/freeze.bend as FZ
import ../curve25519/cong.bend as G
import ../curve25519/xbits.bend as XB

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

def cs_mz(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == True{} : Bool}) -> {FZ.csg(x, cp) == x : List<&2, U32>}:
  +r = F.carry(F.addl(x, cp), 0)
  +c0 = U.lt_one_zero(v(LM.cc(r)), L.subst(Nat, o => {Nat.is_lt(v(LM.cc(r)), o) == True{} : Bool}, one, 1n, h1, hc))
  +cz = U.injective(LM.cc(r), 0, c0)
  %Equal.sym(List<&2, U32>, F.csub_fin(r, x), F.select(LM.cc(r), x, LM.cl(r)), FZ.cs_eta(r, x)) : {_ == x : List<&2, U32>}
  %Equal.cong(U32, List<&2, U32>, z => F.select(z, x, LM.cl(r)), 0, LM.cc(r), Equal.sym(U32, LM.cc(r), 0, cz)) : {_ == x : List<&2, U32>}
  FO.select0(one, h1, 32n, x, LM.cl(r), hx, FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))

def cs_mo(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {FZ.csg(x, cp) == LM.cl(F.carry(F.addl(x, cp), 0)) : List<&2, U32>}:
  +r = F.carry(F.addl(x, cp), 0)
  +co = U.injective(LM.cc(r), 1, Equal.trans(Nat, v(LM.cc(r)), one, 1n, mo_c(one, h1, mm, x, cp, hx, hk, hv, hc), h1))
  %Equal.sym(List<&2, U32>, F.csub_fin(r, x), F.select(LM.cc(r), x, LM.cl(r)), FZ.cs_eta(r, x)) : {_ == LM.cl(r) : List<&2, U32>}
  %Equal.cong(U32, List<&2, U32>, z => F.select(z, x, LM.cl(r)), 1, LM.cc(r), Equal.sym(U32, LM.cc(r), 1, co)) : {_ == LM.cl(r) : List<&2, U32>}
  FO.select1(one, h1, 32n, x, LM.cl(r), hx, FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))

# ---- csub: tight, and value(x) mod M for x < 2 M ----

def cs_okb_by(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {LM.okb(32n, FZ.csg(x, cp), 255n) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), x, cs_mz(one, h1, x, cp, hx, hk, hb)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      hx
    case False{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), LM.cl(F.carry(F.addl(x, cp), 0)), cs_mo(one, h1, mm, x, cp, hx, hk, hv, hb)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      FD.cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk))

def cs_val_by(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +h2m: {Nat.is_lt(FS.value(x), Nat.add(1n+mm, 1n+mm)) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {FS.value(FZ.csg(x, cp)) == Nat.mod(FS.value(x), 1n+mm) : Nat}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), x, cs_mz(one, h1, x, cp, hx, hk, hb)) : {FS.value(_) == Nat.mod(FS.value(x), 1n+mm) : Nat}
      Equal.sym(Nat, Nat.mod(FS.value(x), 1n+mm), FS.value(x), NR.mod_of(0n, mm, FS.value(x), mz(one, h1, mm, x, cp, hx, hk, hv, hb)))
    case False{}:
      +s = LM.cl(F.carry(F.addl(x, cp), 0))
      %Equal.sym(List<&2, U32>, FZ.csg(x, cp), s, cs_mo(one, h1, mm, x, cp, hx, hk, hv, hb)) : {FS.value(_) == Nat.mod(FS.value(x), 1n+mm) : Nat}
      +e1 = mo(one, h1, mm, x, cp, hx, hk, hv, hb)
      +l1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(1n+mm, 1n+mm)) == True{} : Bool}, FS.value(x), Nat.add(FS.value(s), 1n+mm), Equal.sym(Nat, Nat.add(FS.value(s), 1n+mm), FS.value(x), e1), h2m)
      +sl = RD.lt_cancel_r(FS.value(s), 1n+mm, 1n+mm, l1)
      +e2 = Equal.trans(Nat, FS.value(x), Nat.add(FS.value(s), 1n+mm), Nat.add(Nat.mul(1n, 1n+mm), FS.value(s)), Equal.sym(Nat, Nat.add(FS.value(s), 1n+mm), FS.value(x), e1), Equal.trans(Nat, Nat.add(FS.value(s), 1n+mm), Nat.add(1n+mm, FS.value(s)), Nat.add(Nat.mul(1n, 1n+mm), FS.value(s)), NA.add_comm(FS.value(s), 1n+mm), M.cong_l(1n+mm, Nat.mul(1n, 1n+mm), FS.value(s), Equal.sym(Nat, Nat.mul(1n, 1n+mm), 1n+mm, AR.one_mul(1n+mm)))))
      Equal.sym(Nat, Nat.mod(FS.value(x), 1n+mm), FS.value(s), Equal.trans(Nat, Nat.mod(FS.value(x), 1n+mm), Nat.mod(Nat.add(Nat.mul(1n, 1n+mm), FS.value(s)), 1n+mm), FS.value(s), M.cong_mod(1n+mm, FS.value(x), Nat.add(Nat.mul(1n, 1n+mm), FS.value(s)), e2), NR.mod_of(1n, mm, FS.value(s), sl)))

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

def sum_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.cr_limbs(F.carry(F.addl(a, b), 0)), 255n) == True{} : Bool}:
  FD.cr_okb(one, h1, F.addl(a, b), FO.addl_okb(one, h1, a, b, ha, hb))

# a + b < 2 M <= 2^256: no carry out, the limbs hold a + b
def sum_val(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +h2: {Nat.is_le(Nat.add(1n+mm, 1n+mm), T(one)) == True{} : Bool}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}, +la: {Nat.is_lt(FS.value(a), 1n+mm) == True{} : Bool}, +lb: {Nat.is_lt(FS.value(b), 1n+mm) == True{} : Bool}) -> {FS.value(F.cr_limbs(F.carry(F.addl(a, b), 0))) == Nat.add(FS.value(a), FS.value(b)) : Nat}:
  +ys = F.addl(a, b)
  +r = F.carry(ys, 0)
  +V = Nat.add(FS.value(a), FS.value(b))
  +hyo = FO.addl_okb(one, h1, a, b, ha, hb)
  +ev = Equal.trans(Nat, Nat.add(FS.value(LM.cl(r)), LM.shn(32n, v(LM.cc(r)))), FS.value(ys), V, FD.cr_val(one, h1, ys, hyo), PL.addl_val(one, h1, a, b, 255n, 255n, LM.okb_lea(32n, a, 255n, ha), LM.okb_lea(32n, b, 255n, hb), FO.lt32_small(one, h1, Nat.add(255n, 255n), {==})))
  +l2 = N.lt_le_trans(V, Nat.add(1n+mm, 1n+mm), T(one), N.lt_le_trans(V, Nat.add(1n+mm, FS.value(b)), Nat.add(1n+mm, 1n+mm), N.lt_add_r2(FS.value(a), 1n+mm, FS.value(b), la), N.lt_le(Nat.add(1n+mm, FS.value(b)), Nat.add(1n+mm, 1n+mm), N.lt_add_left(FS.value(b), 1n+mm, 1n+mm, lb))), h2)
  +z = RD.last_zero(one, h1, FS.value(LM.cl(r)), v(LM.cc(r)), V, ev, l2, Nat.is_lt(v(LM.cc(r)), one), {==})
  +ev0 = L.subst(Nat, w => {Nat.add(FS.value(LM.cl(r)), LM.shn(32n, w)) == V : Nat}, v(LM.cc(r)), 0n, z, ev)
  Equal.trans(Nat, FS.value(LM.cl(r)), Nat.add(FS.value(LM.cl(r)), 0n), V, Equal.sym(Nat, Nat.add(FS.value(LM.cl(r)), 0n), FS.value(LM.cl(r)), N.add_zero(FS.value(LM.cl(r)))), ev0)

# addm with its constant as a parameter
def addg(+a: List<&2, U32>, +b: List<&2, U32>, +cp: List<&2, U32>) -> List<&2, U32>:
  FZ.csg(F.cr_limbs(F.carry(F.addl(a, b), 0)), cp)

def addg_okb(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, addg(a, b, cp), 255n) == True{} : Bool}:
  +s = F.cr_limbs(F.carry(F.addl(a, b), 0))
  cs_okb_by(one, h1, mm, s, cp, sum_okb(one, h1, a, b, ha, hb), hk, hv, Nat.is_lt(v(LM.cc(F.carry(F.addl(s, cp), 0))), one), {==})

def addg_val(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +h2: {Nat.is_le(Nat.add(1n+mm, 1n+mm), T(one)) == True{} : Bool}, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == T(one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}, +la: {Nat.is_lt(FS.value(a), 1n+mm) == True{} : Bool}, +lb: {Nat.is_lt(FS.value(b), 1n+mm) == True{} : Bool}) -> {FS.value(addg(a, b, cp)) == Nat.mod(Nat.add(FS.value(a), FS.value(b)), 1n+mm) : Nat}:
  +s = F.cr_limbs(F.carry(F.addl(a, b), 0))
  +es = sum_val(one, h1, mm, h2, a, b, ha, hb, la, lb)
  +h2m = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(1n+mm, 1n+mm)) == True{} : Bool}, Nat.add(FS.value(a), FS.value(b)), FS.value(s), Equal.sym(Nat, FS.value(s), Nat.add(FS.value(a), FS.value(b)), es), N.lt_le_trans(Nat.add(FS.value(a), FS.value(b)), Nat.add(1n+mm, FS.value(b)), Nat.add(1n+mm, 1n+mm), N.lt_add_r2(FS.value(a), 1n+mm, FS.value(b), la), N.lt_le(Nat.add(1n+mm, FS.value(b)), Nat.add(1n+mm, 1n+mm), N.lt_add_left(FS.value(b), 1n+mm, 1n+mm, lb))))
  +e1 = cs_val_by(one, h1, mm, s, cp, sum_okb(one, h1, a, b, ha, hb), hk, hv, h2m, Nat.is_lt(v(LM.cc(F.carry(F.addl(s, cp), 0))), one), {==})
  Equal.trans(Nat, FS.value(addg(a, b, cp)), Nat.mod(FS.value(s), 1n+mm), Nat.mod(Nat.add(FS.value(a), FS.value(b)), 1n+mm), e1, M.cong_mod(1n+mm, FS.value(s), Nat.add(FS.value(a), FS.value(b)), es))

def lt_mod(+mm: Nat, +x: Nat) -> {Nat.is_lt(Nat.mod(x, 1n+mm), 1n+mm) == True{} : Bool}:
  NR.dm_lt(mm, x)
