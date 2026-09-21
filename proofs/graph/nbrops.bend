import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/order.bend as O
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../balanced_search_tree/sorted.bend as SO
import ../balanced_search_tree/specops.bend as SP
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./blk.bend as BK
import ./edge.bend as ED
import ./lists.bend as LS
import ./asc.bend as AS
import ./blkops.bend as BO

# Adding / removing one neighbour of one vertex: the block the runtime
# leaves behind (chosen by its own found / room flags), its meaning as the
# specification's sadd / sdel, and its well-formedness.

def lw(+bt: AR.Tree<U32>, +w: U32) -> Nat:
  W.lbs(w, AR.slots(U32, bt), ST.bdeg(bt), 3n)

def fnd(+bt: AR.Tree<U32>, +w: U32) -> Bool:
  SE.found_of(bt, BK.lbb(bt, w), Nat.add(3n, ST.bdeg(bt)), w)

def es(+bt: AR.Tree<U32>) -> List<&2, BE.Entry<U32, Unit>>:
  ST.uset(ST.bents(bt))

def es_sorted(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, Unit, es(bt)) == True{} : Bool}:
  ED.sorted_uset(ST.bents(bt), W.asc_win(ST.bdeg(bt), AR.slots(U32, bt), 3n, ED.bk_asc(bt, bk)))

def e_lbx(+bt: AR.Tree<U32>, +w: U32) -> {LB.lbx(Unit, w, es(bt)) == lw(bt, w) : Nat}:
  Equal.trans(Nat, LB.lbx(Unit, w, es(bt)), W.lbu(w, ST.bents(bt)), lw(bt, w),
    ED.uset_lbx(w, ST.bents(bt)),
    Equal.sym(Nat, lw(bt, w), W.lbu(w, ST.bents(bt)), W.lbs_lbu(w, AR.slots(U32, bt), ST.bdeg(bt), 3n)))

def e_hf(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {fnd(bt, w) == LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w) : Bool}:
  Equal.trans(Bool, fnd(bt, w), S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w),
    Equal.sym(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), fnd(bt, w), ED.blk_found(bt, w, ED.bk_perfect(bt, bk), ED.bk_cap(bt, bk), ED.bk_asc(bt, bk))),
    LB.find_some(Unit, es(bt), w, es_sorted(bt, bk)))

def e_is_some(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {fnd(bt, w) == S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))) : Bool}:
  Equal.sym(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), fnd(bt, w), ED.blk_found(bt, w, ED.bk_perfect(bt, bk), ED.bk_cap(bt, bk), ED.bk_asc(bt, bk)))

def none_of(-V: Data, m: Maybe<&2, V>, +h: {S.is_some(V, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, V>}, L.false_true(Equal.sym(Bool, True{}, False{}, h)))

def lw_lt(+bt: AR.Tree<U32>, +w: U32, +h: {fnd(bt, w) == True{} : Bool}) -> {Nat.is_lt(lw(bt, w), ST.bdeg(bt)) == True{} : Bool}:
  +hin = ED.found_lt(bt, BK.lbb(bt, w), Nat.add(3n, ST.bdeg(bt)), w, Nat.is_lt(BK.lbb(bt, w), Nat.add(3n, ST.bdeg(bt))), {==}, h)
  hin

def lw_le(+bt: AR.Tree<U32>, +w: U32) -> {Nat.is_le(lw(bt, w), ST.bdeg(bt)) == True{} : Bool}:
  W.lbs_le(w, AR.slots(U32, bt), ST.bdeg(bt), 3n)

def is_eq_cmp(+c: Cmp, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(h))

# Replacing a present Unit entry by itself changes nothing.
def is_eq_eq(+a: U32, +b: U32, +h: {Cmp.is_eq(U32.cmp(a, b)) == True{} : Bool}) -> {a == b : U32}:
  O.u32_antisym(a, b, is_eq_cmp(U32.cmp(a, b), h))

def upd_uset_same(+ws: List<&2, U32>, +l: Nat, +w: U32, +h: {LB.eq_at(ws, l, w) == True{} : Bool}) -> {LB.upd_at(Unit, ST.uset(ws), l, BE.Entry{w, Unit{}}) == ST.uset(ws) : List<&2, BE.Entry<U32, Unit>>}:
  match ws l:
    case Nil{} l0:
      Empty.absurd({LB.upd_at(Unit, Nil{}, l0, BE.Entry{w, Unit{}}) == Nil{} : List<&2, BE.Entry<U32, Unit>>}, L.false_true(h))
    case Con{+x, +t} 0n:
      Equal.cong(U32, List<&2, BE.Entry<U32, Unit>>, z => Con{BE.Entry{z, Unit{}}, ST.uset(t)}, w, x, Equal.sym(U32, x, w, is_eq_eq(x, w, h)))
    case Con{+x, +t} 1n+p:
      LL.cons_cong(BE.Entry<U32, Unit>, BE.Entry{x, Unit{}}, LB.upd_at(Unit, ST.uset(t), p, BE.Entry{w, Unit{}}), ST.uset(t), upd_uset_same(t, p, w, h))

# ---- removal ----

def dsel(+bt: AR.Tree<U32>, +w: U32, f: Bool) -> AR.Tree<U32>:
  match f:
    case True{}:
      BO.bdel(bt, lw(bt, w))
    case False{}:
      bt

def dsem(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}) -> {es(dsel(bt, w, f)) == GS.sdel(w, es(bt)) : List<&2, BE.Entry<U32, Unit>>}:
  match f:
    case True{}:
      +l = lw(bt, w)
      +hf = Equal.trans(Bool, LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w), fnd(bt, w), True{}, Equal.sym(Bool, fnd(bt, w), LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w), e_hf(bt, w, bk)), ef)
      Equal.trans(List<&2, BE.Entry<U32, Unit>>, ST.uset(ST.bents(BO.bdel(bt, l))), ST.uset(LS.dl(ST.bents(bt), l)), GS.sdel(w, es(bt)),
        Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, Unit>>, z => ST.uset(z), ST.bents(BO.bdel(bt, l)), LS.dl(ST.bents(bt), l), BO.del_bents(bt, l, bk, lw_lt(bt, w, ef))),
        Equal.trans(List<&2, BE.Entry<U32, Unit>>, ST.uset(LS.dl(ST.bents(bt), l)), LB.del_at(Unit, es(bt), l), GS.sdel(w, es(bt)),
          LS.uset_dl(ST.bents(bt), l),
          L.subst(Nat, z => {LB.del_at(Unit, es(bt), z) == GS.sdel(w, es(bt)) : List<&2, BE.Entry<U32, Unit>>}, LB.lbx(Unit, w, es(bt)), l, e_lbx(bt, w),
            LS.del_found(Unit, es(bt), w, es_sorted(bt, bk), hf))))
    case False{}:
      Equal.sym(List<&2, BE.Entry<U32, Unit>>, GS.sdel(w, es(bt)), es(bt),
        LS.del_absent(Unit, es(bt), w, none_of(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt)), Equal.trans(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), fnd(bt, w), False{}, Equal.sym(Bool, fnd(bt, w), S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), e_is_some(bt, w, bk)), ef))))

def dsel_ok(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}) -> {ST.blk_ok(dsel(bt, w, f)) == True{} : Bool}:
  match f:
    case True{}:
      BO.del_ok(bt, lw(bt, w), bk, lw_lt(bt, w, ef))
    case False{}:
      bk

# ---- addition ----

def asel(+bt: AR.Tree<U32>, +w: U32, f: Bool, r: Bool) -> AR.Tree<U32>:
  match f r:
    case True{} r0:
      bt
    case False{} True{}:
      BO.bput(bt, lw(bt, w), w)
    case False{} False{}:
      BO.bput(BO.bgrow(bt), lw(bt, w), w)

def room(+bt: AR.Tree<U32>) -> Bool:
  Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt))

# An absent w inserted at its lower bound is the specification's sadd.
def ins_sem(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +ef: {fnd(bt, w) == False{} : Bool}) -> {ST.uset(LS.il(ST.bents(bt), lw(bt, w), w)) == GS.sadd(w, es(bt)) : List<&2, BE.Entry<U32, Unit>>}:
  +l = lw(bt, w)
  Equal.trans(List<&2, BE.Entry<U32, Unit>>, ST.uset(LS.il(ST.bents(bt), l, w)), LB.ins_at(Unit, es(bt), l, BE.Entry{w, Unit{}}), GS.sadd(w, es(bt)),
    LS.uset_il(ST.bents(bt), l, w),
    L.subst(Nat, z => {LB.ins_at(Unit, es(bt), z, BE.Entry{w, Unit{}}) == GS.sadd(w, es(bt)) : List<&2, BE.Entry<U32, Unit>>}, LB.lbx(Unit, w, es(bt)), l, e_lbx(bt, w),
      LB.ins_new(Unit, es(bt), w, Unit{}, none_of(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt)), Equal.trans(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), fnd(bt, w), False{}, Equal.sym(Bool, fnd(bt, w), S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, w, es(bt))), e_is_some(bt, w, bk)), ef)))))

def ins_asc(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +ef: {fnd(bt, w) == False{} : Bool}) -> {ST.asc(LS.il(ST.bents(bt), lw(bt, w), w)) == True{} : Bool}:
  LS.asc_back(LS.il(ST.bents(bt), lw(bt, w), w),
    L.subst(List<&2, BE.Entry<U32, Unit>>, z => {SO.sorted(~U32, ~U32.cmp, Unit, z) == True{} : Bool}, GS.sadd(w, es(bt)), ST.uset(LS.il(ST.bents(bt), lw(bt, w), w)), Equal.sym(List<&2, BE.Entry<U32, Unit>>, ST.uset(LS.il(ST.bents(bt), lw(bt, w), w)), GS.sadd(w, es(bt)), ins_sem(bt, w, bk, ef)),
      SP.sorted_ins(~U32, ~U32.cmp, ~O.u32_order, Unit, es(bt), w, Unit{}, es_sorted(bt, bk))))

def grow_room(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(3n, ST.bdeg(BO.bgrow(bt))), ST.bsize(BO.bgrow(bt))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(3n, z), ST.bsize(BO.bgrow(bt))) == True{} : Bool}, ST.bdeg(bt), ST.bdeg(BO.bgrow(bt)), Equal.sym(Nat, ST.bdeg(BO.bgrow(bt)), ST.bdeg(bt), BO.grow_deg(bt, bk)),
    L.subst(Nat, z => {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), z) == True{} : Bool}, SC.pow2(1n+ST.blcap(bt)), ST.bsize(BO.bgrow(bt)), Equal.sym(Nat, ST.bsize(BO.bgrow(bt)), SC.pow2(1n+ST.blcap(bt)), BO.grow_size(bt, bk, h30)),
      N.le_lt_trans(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt)), SC.pow2(1n+ST.blcap(bt)), ED.bk_cap(bt, bk), N.pow2_lt_succ(ST.blcap(bt)))))

def glw(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {Nat.is_le(lw(bt, w), ST.bdeg(BO.bgrow(bt))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(lw(bt, w), z) == True{} : Bool}, ST.bdeg(bt), ST.bdeg(BO.bgrow(bt)), Equal.sym(Nat, ST.bdeg(BO.bgrow(bt)), ST.bdeg(bt), BO.grow_deg(bt, bk)), lw_le(bt, w))

def gil(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {LS.il(ST.bents(BO.bgrow(bt)), lw(bt, w), w) == LS.il(ST.bents(bt), lw(bt, w), w) : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, z => LS.il(z, lw(bt, w), w), ST.bents(BO.bgrow(bt)), ST.bents(bt), BO.grow_bents(bt, bk))

# The room / growth premise the runtime needs: a full block can still double.
def RoomOK(+bt: AR.Tree<U32>) -> Type:
  {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}

def h30_of(+bt: AR.Tree<U32>, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, +er: {room(bt) == False{} : Bool}) -> {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}:
  L.subst(Bool, b => {Bool.or(b, Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, room(bt), False{}, er, hr)

def asem(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}, r: Bool, +er: {room(bt) == r : Bool}) -> {es(asel(bt, w, f, r)) == GS.sadd(w, es(bt)) : List<&2, BE.Entry<U32, Unit>>}:
  match f r:
    case True{} r0:
      +hf = Equal.trans(Bool, LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w), fnd(bt, w), True{}, Equal.sym(Bool, fnd(bt, w), LB.eq_at(LB.keys_of(Unit, es(bt)), LB.lbx(Unit, w, es(bt)), w), e_hf(bt, w, bk)), ef)
      +hf2 = L.subst(List<&2, U32>, z => {LB.eq_at(z, LB.lbx(Unit, w, es(bt)), w) == True{} : Bool}, LB.keys_of(Unit, es(bt)), ST.bents(bt), ED.uset_keys(ST.bents(bt)), hf)
      Equal.sym(List<&2, BE.Entry<U32, Unit>>, GS.sadd(w, es(bt)), es(bt),
        Equal.trans(List<&2, BE.Entry<U32, Unit>>, GS.sadd(w, es(bt)), LB.upd_at(Unit, es(bt), LB.lbx(Unit, w, es(bt)), BE.Entry{w, Unit{}}), es(bt),
          Equal.sym(List<&2, BE.Entry<U32, Unit>>, LB.upd_at(Unit, es(bt), LB.lbx(Unit, w, es(bt)), BE.Entry{w, Unit{}}), GS.sadd(w, es(bt)), LS.ins_old(Unit, es(bt), w, Unit{}, hf)),
          upd_uset_same(ST.bents(bt), LB.lbx(Unit, w, es(bt)), w, hf2)))
    case False{} True{}:
      Equal.trans(List<&2, BE.Entry<U32, Unit>>, ST.uset(ST.bents(BO.bput(bt, lw(bt, w), w))), ST.uset(LS.il(ST.bents(bt), lw(bt, w), w)), GS.sadd(w, es(bt)),
        Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, Unit>>, z => ST.uset(z), ST.bents(BO.bput(bt, lw(bt, w), w)), LS.il(ST.bents(bt), lw(bt, w), w), BO.put_bents(bt, lw(bt, w), w, bk, lw_le(bt, w), er)),
        ins_sem(bt, w, bk, ef))
    case False{} False{}:
      +g = BO.bgrow(bt)
      +h30 = h30_of(bt, hr, er)
      +gk = BO.grow_ok(bt, bk, h30)
      Equal.trans(List<&2, BE.Entry<U32, Unit>>, ST.uset(ST.bents(BO.bput(g, lw(bt, w), w))), ST.uset(LS.il(ST.bents(bt), lw(bt, w), w)), GS.sadd(w, es(bt)),
        Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, Unit>>, z => ST.uset(z), ST.bents(BO.bput(g, lw(bt, w), w)), LS.il(ST.bents(bt), lw(bt, w), w),
          Equal.trans(List<&2, U32>, ST.bents(BO.bput(g, lw(bt, w), w)), LS.il(ST.bents(g), lw(bt, w), w), LS.il(ST.bents(bt), lw(bt, w), w),
            BO.put_bents(g, lw(bt, w), w, gk, glw(bt, w, bk), grow_room(bt, bk, h30)),
            gil(bt, w, bk))),
        ins_sem(bt, w, bk, ef))

def asel_ok(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}, r: Bool, +er: {room(bt) == r : Bool}) -> {ST.blk_ok(asel(bt, w, f, r)) == True{} : Bool}:
  match f r:
    case True{} r0:
      bk
    case False{} True{}:
      BO.put_ok(bt, lw(bt, w), w, bk, lw_le(bt, w), er, ins_asc(bt, w, bk, ef))
    case False{} False{}:
      +g = BO.bgrow(bt)
      +h30 = h30_of(bt, hr, er)
      BO.put_ok(g, lw(bt, w), w, BO.grow_ok(bt, bk, h30), glw(bt, w, bk), grow_room(bt, bk, h30),
        L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, LS.il(ST.bents(bt), lw(bt, w), w), LS.il(ST.bents(g), lw(bt, w), w), Equal.sym(List<&2, U32>, LS.il(ST.bents(g), lw(bt, w), w), LS.il(ST.bents(bt), lw(bt, w), w), gil(bt, w, bk)), ins_asc(bt, w, bk, ef)))

# ---- the adjacency array ----

def upd_id(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +x: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, t), j) == Some{x} : Maybe<&2, T>}) -> {AR.upd(T, d, t, j, x) == t : AR.Tree<T>}:
  BK.tupd_self(T, d, t, j, x, hj, pf, hx, AR.ndec(d, j), {==})

# Swap the block at i for a placeholder, then store a NEW block b2 at i.
def swap_put(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +b2: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}) -> {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, AR.thaw(U32, b2)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), b2)) : Array<Array<U32>>}:
  +j = U32.to_nat(i)
  +at1 = AR.upd(AR.Tree<U32>, d, at, j, BK.leaf0())
  Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, A2.thaw2(at1), i, AR.thaw(U32, b2)), A2.thaw2(AR.upd(AR.Tree<U32>, d, at1, j, b2)), A2.thaw2(AR.upd(AR.Tree<U32>, d, at, j, b2)),
    A2.set2(d, at1, i, b2, BK.leaf0(), hd, hi, BK.upd_nth_same(AR.Tree<U32>, d, at, j, BK.leaf0(), hi, pf), AR.upd_perfect(AR.Tree<U32>, d, at, j, BK.leaf0(), pf)),
    Equal.cong(AR.Tree<AR.Tree<U32>>, Array<Array<U32>>, z => A2.thaw2(z), AR.upd(AR.Tree<U32>, d, at1, j, b2), AR.upd(AR.Tree<U32>, d, at, j, b2), BK.tupd_tupd(AR.Tree<U32>, d, at, j, BK.leaf0(), b2, AR.ndec(d, j))))

def keep_back(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}) -> {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, AR.thaw(U32, bt)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), bt)) : Array<Array<U32>>}:
  swap_put(d, at, i, bt, hd, hi, pf)

def room_eq(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {U32.is_lt(G.ent_end(BK.v0(bt)), BK.v1(bt)) == room(bt) : Bool}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +hd = ED.bk_lt32(bt, bk)
  +bcap = ED.bk_cap(bt, bk)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, hd), N.le_lt_trans(dg, Nat.add(2n, dg), SC.pow2(lc), BK.le_plus(2n, dg), N.lt_le_trans(Nat.add(2n, dg), Nat.add(3n, dg), SC.pow2(lc), N.lt_succ(Nat.add(2n, dg)), bcap)))
  +et = Equal.trans(Nat, U32.to_nat(G.ent_end(BK.v0(bt))), U32.to_nat(U32.from_nat(Nat.add(3n, dg))), Nat.add(3n, dg),
    Equal.cong(U32, Nat, z => U32.to_nat(U32.inc(U32.inc(U32.inc(z)))), BK.v0(bt), U32.from_nat(dg), Equal.sym(U32, U32.from_nat(dg), BK.v0(bt), e0)),
    U.to_nat_from_nat(Nat.add(3n, dg), 1n+lc, N.lt_succ_le_succ(lc, 32n, hd), N.le_lt_trans(Nat.add(3n, dg), SC.pow2(lc), SC.pow2(1n+lc), bcap, N.pow2_lt_succ(lc))))
  Equal.trans(Bool, U32.is_lt(G.ent_end(BK.v0(bt)), BK.v1(bt)), Nat.is_lt(U32.to_nat(G.ent_end(BK.v0(bt))), ST.bsize(bt)), room(bt),
    U.is_lt_nat(G.ent_end(BK.v0(bt)), BK.v1(bt)),
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, ST.bsize(bt)), U32.to_nat(G.ent_end(BK.v0(bt))), Nat.add(3n, dg), et))

# the facts every adjacency update needs about slot i and its block
def AdjAt(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>) -> Type:
  {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool} & {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}

# ---- removing a neighbour ----

def dn_case(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bk: {ST.blk_ok(bt) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}) -> {G.del_in5(A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, AR.thaw(U32, bt), BK.v0(bt), U32.from_nat(BK.lbb(bt, w)), f) == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), dsel(bt, w, f))), f} : G.Upd}:
  match f:
    case True{}:
      %Equal.sym(Array<U32>, G.blk_del(AR.thaw(U32, bt), BK.v0(bt), U32.from_nat(BK.lbb(bt, w))), AR.thaw(U32, BO.bdel(bt, lw(bt, w))), BO.blk_del_ok(bt, lw(bt, w), bk, lw_lt(bt, w, ef))) : {G.UP{Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, _), True{}} == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bdel(bt, lw(bt, w)))), True{}} : G.Upd}
      Equal.cong(Array<Array<U32>>, G.Upd, z => G.UP{z, True{}}, Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, AR.thaw(U32, BO.bdel(bt, lw(bt, w)))), A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bdel(bt, lw(bt, w)))), swap_put(d, at, i, BO.bdel(bt, lw(bt, w)), hd, hi, pf))
    case False{}:
      Equal.cong(Array<Array<U32>>, G.Upd, z => G.UP{z, False{}}, Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, AR.thaw(U32, bt)), A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), bt)), keep_back(d, at, i, bt, hd, hi, hx, pf))

# Removing w from the block of slot i: the runtime result is the mirror.
def del_nbr_ok(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {G.del_nbr(A2.thaw2(at), i, w) == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), dsel(bt, w, fnd(bt, w)))), fnd(bt, w)} : G.Upd}:
  +at1 = AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(at), i, AR.thaw(U32, BK.leaf0())), (A2.thaw2(at1), AR.thaw(U32, bt)), A2.swap2(d, at, i, BK.leaf0(), bt, hd, hi, hx, pf)) : {G.del_in2(i, w, _) == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), dsel(bt, w, fnd(bt, w)))), fnd(bt, w)} : G.Upd}
  %Equal.sym(G.Hdr, G.header(AR.thaw(U32, bt)), G.HD{AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt)}, BK.header_ok(bt, ED.bk_lt32(bt, bk), ED.bk_two(bt, bk), ED.bk_perfect(bt, bk))) : {G.del_in3(A2.thaw2(at1), i, w, _) == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), dsel(bt, w, fnd(bt, w)))), fnd(bt, w)} : G.Upd}
  %Equal.sym(G.Loc, G.blk_find(AR.thaw(U32, bt), BK.v0(bt), BK.v2(bt), w), G.LC{AR.thaw(U32, bt), U32.from_nat(BK.lbb(bt, w)), fnd(bt, w)}, BK.blk_find_ok(bt, w, ED.bk_lt32(bt, bk), ED.bk_perfect(bt, bk), ED.bk_cap(bt, bk), ED.bk_asc(bt, bk))) : {G.del_in4(A2.thaw2(at1), i, BK.v0(bt), _) == G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), dsel(bt, w, fnd(bt, w)))), fnd(bt, w)} : G.Upd}
  dn_case(d, at, i, bt, w, hd, hi, hx, pf, bk, fnd(bt, w), {==})

# ---- adding a neighbour ----

def an_room(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, r: Bool, +er: {room(bt) == r : Bool}) -> {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, G.blk_add(AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt), U32.from_nat(BK.lbb(bt, w)), w, r)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, False{}, r))) : Array<Array<U32>>}:
  match r:
    case True{}:
      +at1 = AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())
      %Equal.sym(Array<U32>, G.blk_put(AR.thaw(U32, bt), BK.v0(bt), U32.from_nat(BK.lbb(bt, w)), w), AR.thaw(U32, BO.bput(bt, lw(bt, w), w)), BO.blk_put_ok(bt, lw(bt, w), w, bk, lw_le(bt, w), er)) : {Array.set(Array<U32>, A2.thaw2(at1), i, _) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bput(bt, lw(bt, w), w))) : Array<Array<U32>>}
      swap_put(d, at, i, BO.bput(bt, lw(bt, w), w), hd, hi, pf)
    case False{}:
      +at1 = AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())
      +g = BO.bgrow(bt)
      +h30 = h30_of(bt, hr, er)
      %Equal.sym(Array<U32>, G.blk_grow(AR.thaw(U32, bt), BK.v1(bt), BK.v2(bt)), AR.thaw(U32, g), BO.blk_grow_ok(bt, bk, h30)) : {Array.set(Array<U32>, A2.thaw2(at1), i, G.blk_put(_, BK.v0(bt), U32.from_nat(BK.lbb(bt, w)), w)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bput(g, lw(bt, w), w))) : Array<Array<U32>>}
      %BO.grow_v0(bt, bk) : {Array.set(Array<U32>, A2.thaw2(at1), i, G.blk_put(AR.thaw(U32, g), _, U32.from_nat(BK.lbb(bt, w)), w)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bput(g, lw(bt, w), w))) : Array<Array<U32>>}
      %Equal.sym(Array<U32>, G.blk_put(AR.thaw(U32, g), BK.v0(g), U32.from_nat(BK.lbb(bt, w)), w), AR.thaw(U32, BO.bput(g, lw(bt, w), w)), BO.blk_put_ok(g, lw(bt, w), w, BO.grow_ok(bt, bk, h30), glw(bt, w, bk), grow_room(bt, bk, h30))) : {Array.set(Array<U32>, A2.thaw2(at1), i, _) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BO.bput(g, lw(bt, w), w))) : Array<Array<U32>>}
      swap_put(d, at, i, BO.bput(g, lw(bt, w), w), hd, hi, pf)

def an_case(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, f: Bool, +ef: {fnd(bt, w) == f : Bool}) -> {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, G.add_in5(AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt), U32.from_nat(BK.lbb(bt, w)), w, f)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, f, room(bt)))) : Array<Array<U32>>}:
  match f:
    case True{}:
      keep_back(d, at, i, bt, hd, hi, hx, pf)
    case False{}:
      %Equal.sym(Bool, U32.is_lt(G.ent_end(BK.v0(bt)), BK.v1(bt)), room(bt), room_eq(bt, bk)) : {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())), i, G.blk_add(AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt), U32.from_nat(BK.lbb(bt, w)), w, _)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, False{}, room(bt)))) : Array<Array<U32>>}
      an_room(d, at, i, bt, w, hd, hi, pf, bk, hr, room(bt), {==})

# Adding w to the block of slot i: the runtime result is the mirror.
def add_nbr_ok(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}) -> {G.add_nbr(A2.thaw2(at), i, w) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, fnd(bt, w), room(bt)))) : Array<Array<U32>>}:
  +at1 = AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(at), i, AR.thaw(U32, BK.leaf0())), (A2.thaw2(at1), AR.thaw(U32, bt)), A2.swap2(d, at, i, BK.leaf0(), bt, hd, hi, hx, pf)) : {G.add_in2(i, w, _) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, fnd(bt, w), room(bt)))) : Array<Array<U32>>}
  %Equal.sym(G.Hdr, G.header(AR.thaw(U32, bt)), G.HD{AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt)}, BK.header_ok(bt, ED.bk_lt32(bt, bk), ED.bk_two(bt, bk), ED.bk_perfect(bt, bk))) : {G.add_in3(A2.thaw2(at1), i, w, _) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, fnd(bt, w), room(bt)))) : Array<Array<U32>>}
  %Equal.sym(G.Loc, G.blk_find(AR.thaw(U32, bt), BK.v0(bt), BK.v2(bt), w), G.LC{AR.thaw(U32, bt), U32.from_nat(BK.lbb(bt, w)), fnd(bt, w)}, BK.blk_find_ok(bt, w, ED.bk_lt32(bt, bk), ED.bk_perfect(bt, bk), ED.bk_cap(bt, bk), ED.bk_asc(bt, bk))) : {G.add_in4(A2.thaw2(at1), i, BK.v0(bt), BK.v1(bt), BK.v2(bt), w, _) == A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), asel(bt, w, fnd(bt, w), room(bt)))) : Array<Array<U32>>}
  an_case(d, at, i, bt, w, hd, hi, hx, pf, bk, hr, fnd(bt, w), {==})
