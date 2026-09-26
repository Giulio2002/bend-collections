import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ./w64div.bend as W64D
import ./w64add.bend as WA
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64dm.bend as DM

# DivMod.quot and DivMod.rem of spec/math/w64.bend: the 32-bit divisor by
# div32, the wide one by the corrected quotient of w64dm.bend.

def hd_small(+bl: U32, +bh: U32, +hb: {X.is_zero(WU.U64{bl, bh}) == False{} : Bool}, +hz: {U32.is_zero(bh) == True{} : Bool}) -> {U32.is_zero(bl) == False{} : Bool}:
  Equal.trans(Bool, U32.is_zero(bl), Bool.and(U32.is_zero(bl), True{}), False{}, Equal.sym(Bool, Bool.and(U32.is_zero(bl), True{}), U32.is_zero(bl), U.and_true(U32.is_zero(bl))), L.subst(Bool, t => {Bool.and(U32.is_zero(bl), t) == False{} : Bool}, U32.is_zero(bh), True{}, hz, hb))

def vb_small(+bl: U32, +bh: U32, +hz: {U32.is_zero(bh) == True{} : Bool}) -> {SW.value(WU.U64{bl, bh}) == DM.v(bl) : Nat}:
  +e0 = N.eq_from_is_eq(DM.v(bh), 0n, Equal.trans(Bool, Nat.is_eq(DM.v(bh), 0n), U32.is_zero(bh), True{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(DM.v(bh), 0n), LW.zero_nat(bh)), hz))
  Equal.trans(Nat, Nat.add(DM.v(bl), C.shift(32n, DM.v(bh))), Nat.add(DM.v(bl), C.shift(32n, 0n)), DM.v(bl), Equal.cong(Nat, Nat, z => Nat.add(DM.v(bl), C.shift(32n, z)), DM.v(bh), 0n, e0), Equal.trans(Nat, Nat.add(DM.v(bl), C.shift(32n, 0n)), Nat.add(DM.v(bl), 0n), DM.v(bl), Equal.cong(Nat, Nat, z => Nat.add(DM.v(bl), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(DM.v(bl))))

def vb_pos(+bl: U32, +bh: U32, +hz: {U32.is_zero(bh) == False{} : Bool}) -> {Nat.is_le(1n, SW.value(WU.U64{bl, bh})) == True{} : Bool}:
  +h1 = WA.pos_ne(DM.v(bh), Equal.trans(Bool, Nat.is_eq(DM.v(bh), 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(DM.v(bh), 0n), LW.zero_nat(bh)), hz))
  N.le_trans(1n, DM.v(bh), SW.value(WU.U64{bl, bh}), h1, N.le_trans(DM.v(bh), C.shift(32n, DM.v(bh)), SW.value(WU.U64{bl, bh}), WW.shift_ge(32n, DM.v(bh)), L.subst(Nat, z => {Nat.is_le(C.shift(32n, DM.v(bh)), z) == True{} : Bool}, Nat.add(C.shift(32n, DM.v(bh)), DM.v(bl)), SW.value(WU.U64{bl, bh}), N.add_comm(C.shift(32n, DM.v(bh)), DM.v(bl)), N.le_add_right(C.shift(32n, DM.v(bh)), DM.v(bl)))))

def dmq_s(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +hb: {X.is_zero(WU.U64{bl, bh}) == False{} : Bool}, +hz: {U32.is_zero(bh) == True{} : Bool}) -> {SW.value(X.pfst(X.dm_pick(WU.U64{al, ah}, WU.U64{bl, bh}, True{}))) == Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}:
  Equal.trans(Nat, SW.value(X.fst_q(X.div32(WU.U64{al, ah}, bl))), Nat.div(SW.value(WU.U64{al, ah}), DM.v(bl)), Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})), W64D.div32_quot(WU.U64{al, ah}, bl, hd_small(bl, bh, hb, hz)), Equal.cong(Nat, Nat, t => Nat.div(SW.value(WU.U64{al, ah}), t), DM.v(bl), SW.value(WU.U64{bl, bh}), Equal.sym(Nat, SW.value(WU.U64{bl, bh}), DM.v(bl), vb_small(bl, bh, hz))))

def dmq_bg(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +e: U32, +hb: {X.is_zero(WU.U64{bl, bh}) == False{} : Bool}, +hz: {U32.is_zero(bh) == False{} : Bool}) -> {SW.value(WU.U64{X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e), 0}) == Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}:
  +bp = Nat.sub(SW.value(WU.U64{bl, bh}), 1n)
  +hB = Equal.sym(Nat, 1n+bp, SW.value(WU.U64{bl, bh}), N.sub_add(SW.value(WU.U64{bl, bh}), 1n, vb_pos(bl, bh, hz)))
  dp = DM.dm_pair(one, h1, al, ah, bl, bh, e, hz, bp, hB)
  +d1 = DM.pr1({Nat.div(SW.value(WU.U64{al, ah}), 1n+bp) == DM.v(DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)) : Nat}, {Nat.mod(SW.value(WU.U64{al, ah}), 1n+bp) == Nat.sub(SW.value(WU.U64{al, ah}), Nat.mul(DM.v(DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), 1n+bp)) : Nat}, dp)
  +eq = Equal.cong(U32, Nat, t => DM.v(t), X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e), DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295), DM.impl_qs(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e))
  Equal.trans(Nat, SW.value(WU.U64{X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e), 0}), DM.v(X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e)), Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})), DM.u32_0(X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e)), Equal.trans(Nat, DM.v(X.q_start(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e)), DM.v(DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})), eq, Equal.trans(Nat, DM.v(DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), Nat.div(SW.value(WU.U64{al, ah}), 1n+bp), Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})), Equal.sym(Nat, Nat.div(SW.value(WU.U64{al, ah}), 1n+bp), DM.v(DM.QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), d1), Equal.cong(Nat, Nat, t => Nat.div(SW.value(WU.U64{al, ah}), t), 1n+bp, SW.value(WU.U64{bl, bh}), Equal.sym(Nat, SW.value(WU.U64{bl, bh}), 1n+bp, hB)))))



def dmq_b(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +hb: {X.is_zero(WU.U64{bl, bh}) == False{} : Bool}, +hz: {U32.is_zero(bh) == False{} : Bool}) -> {SW.value(X.pfst(X.dm_pick(WU.U64{al, ah}, WU.U64{bl, bh}, False{}))) == Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}:
  dmq_bg(one, h1, al, ah, bl, bh, X.q_clamp(X.fst_q(X.div32(X.shr96_t(WU.U64{X.hi(WU.U64{al, ah}), 0}, X.lo(WU.U64{al, ah}), X.bitlen(bh)), X.lo(X.shr_t(WU.U64{bl, bh}, X.bitlen(bh)))))), hb, hz)

def dmq(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +hb: {X.is_zero(WU.U64{bl, bh}) == False{} : Bool}, +z: Bool, +hz: {U32.is_zero(bh) == z : Bool}) -> {SW.value(X.pfst(X.dm_pick(WU.U64{al, ah}, WU.U64{bl, bh}, z))) == Nat.div(SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}:
  match z:
    case True{}:
      dmq_s(one, h1, al, ah, bl, bh, hb, hz)
    case False{}:
      dmq_b(one, h1, al, ah, bl, bh, hb, hz)

def divmod_quot(+a: WU.U64, +b: WU.U64, +hb: {X.is_zero(b) == False{} : Bool}) -> SW.DivMod.quot(a, b, hb):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      dmq(1n, {==}, al, ah, bl, bh, hb, U32.is_zero(bh), {==})

