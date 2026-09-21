import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../lib/u32half.bend as H2
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./ops.bend as OP
import ./blk.bend as BK
import ./edge.bend as ED
import ./blkops.bend as BO
import ./nbrops.bend as NO
import ./eops.bend as EO
import ./gstep.bend as GT
import ./ucore.bend as UC
import ./shift.bend as SH

import ./rmedge.bend as RM

# add_edge: refinement, invariant preservation and the measure bound.
# The room premise `3 + mu < 2^q` with q <= 30 guarantees that a full
# adjacency block (2^lcap words) has lcap <= 30 and can still double.

# ---- degree measure ----

def mdeg_nth(+bs: List<&2, AR.Tree<U32>>, +l: Nat) -> {Nat.is_le(ST.bdeg(ED.bnth(bs, l)), GT.mdeg(bs)) == True{} : Bool}:
  match bs l:
    case Nil{} l0:
      {==}
    case Con{+b0, +t} 0n:
      GT.le_max_l(ST.bdeg(b0), GT.mdeg(t))
    case Con{+b0, +t} 1n+p:
      N.le_trans(ST.bdeg(ED.bnth(t, p)), GT.mdeg(t), Nat.max(ST.bdeg(b0), GT.mdeg(t)), mdeg_nth(t, p), GT.le_max_r(ST.bdeg(b0), GT.mdeg(t)))

def mdeg_upd_bound(+bs: List<&2, AR.Tree<U32>>, +l: Nat, +b: AR.Tree<U32>, +m: Nat, +hb: {Nat.is_le(ST.bdeg(b), m) == True{} : Bool}, +hm: {Nat.is_le(GT.mdeg(bs), m) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(SC.update(AR.Tree<U32>, bs, l, b)), m) == True{} : Bool}:
  match bs l:
    case Nil{} l0:
      hm
    case Con{+b0, +t} 0n:
      GT.max_le(ST.bdeg(b), GT.mdeg(t), m, hb, N.le_trans(GT.mdeg(t), Nat.max(ST.bdeg(b0), GT.mdeg(t)), m, GT.le_max_r(ST.bdeg(b0), GT.mdeg(t)), hm))
    case Con{+b0, +t} 1n+p:
      GT.max_le(ST.bdeg(b0), GT.mdeg(SC.update(AR.Tree<U32>, t, p, b)), m,
        N.le_trans(ST.bdeg(b0), Nat.max(ST.bdeg(b0), GT.mdeg(t)), m, GT.le_max_l(ST.bdeg(b0), GT.mdeg(t)), hm),
        mdeg_upd_bound(t, p, b, m, hb, N.le_trans(GT.mdeg(t), Nat.max(ST.bdeg(b0), GT.mdeg(t)), m, GT.le_max_r(ST.bdeg(b0), GT.mdeg(t)), hm)))

# ---- the room premise ----

def pow2_inv_c(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(SC.pow2(a), SC.pow2(a)), True{}, Equal.sym(Bool, Nat.is_lt(SC.pow2(a), SC.pow2(a)), False{}, N.lt_irrefl(SC.pow2(a))),
        N.lt_le_trans(SC.pow2(a), SC.pow2(b), SC.pow2(a), h, N.pow2_mono(b, a, N.not_lt_le(a, b, ec))))))

def pow2_inv(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  pow2_inv_c(a, b, h, Nat.is_lt(a, b), {==})

def room_c(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +m: Nat, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hd: {Nat.is_le(ST.bdeg(bt), m) == True{} : Bool}, +hm: {Nat.is_lt(Nat.add(3n, m), SC.pow2(q)) == True{} : Bool}, r: Bool, +er: {NO.room(bt) == r : Bool}) -> {Bool.or(NO.room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}:
  match r:
    case True{}:
      L.subst(Bool, b => {Bool.or(b, Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, True{}, NO.room(bt), Equal.sym(Bool, NO.room(bt), True{}, er), {==})
    case False{}:
      +hs = L.subst(Nat, z => {Nat.is_le(z, Nat.add(3n, ST.bdeg(bt))) == True{} : Bool}, ST.bsize(bt), SC.pow2(ST.blcap(bt)), N.eq_from_is_eq(ST.bsize(bt), SC.pow2(ST.blcap(bt)), ED.bk_size(bt, bk)), N.not_lt_le(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt), er))
      +hp = N.le_lt_trans(SC.pow2(ST.blcap(bt)), Nat.add(3n, m), SC.pow2(q), N.le_trans(SC.pow2(ST.blcap(bt)), Nat.add(3n, ST.bdeg(bt)), Nat.add(3n, m), hs, N.le_add_left(ST.bdeg(bt), m, 3n, hd)), hm)
      L.subst(Bool, b => {Bool.or(b, Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, False{}, NO.room(bt), Equal.sym(Bool, NO.room(bt), False{}, er),
        N.lt_le(ST.blcap(bt), 30n, N.lt_le_trans(ST.blcap(bt), q, 30n, pow2_inv(ST.blcap(bt), q, hp), hq)))

def room_of(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +m: Nat, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hd: {Nat.is_le(ST.bdeg(bt), m) == True{} : Bool}, +hm: {Nat.is_lt(Nat.add(3n, m), SC.pow2(q)) == True{} : Bool}) -> {Bool.or(NO.room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}:
  room_c(bt, bk, m, q, hq, hd, hm, NO.room(bt), {==})

# Adding a neighbour raises the degree by at most one.
def asel_deg(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Bool.or(NO.room(bt), Nat.is_le(ST.blcap(bt), 30n)) == True{} : Bool}, f: Bool, r: Bool, +er: {NO.room(bt) == r : Bool}) -> {Nat.is_le(ST.bdeg(NO.asel(bt, w, f, r)), 1n+ST.bdeg(bt)) == True{} : Bool}:
  match f r:
    case True{} r0:
      N.le_succ(ST.bdeg(bt))
    case False{} True{}:
      L.subst(Nat, z => {Nat.is_le(z, 1n+ST.bdeg(bt)) == True{} : Bool}, 1n+ST.bdeg(bt), ST.bdeg(BO.bput(bt, NO.lw(bt, w), w)), Equal.sym(Nat, ST.bdeg(BO.bput(bt, NO.lw(bt, w), w)), 1n+ST.bdeg(bt), BO.put_deg(bt, NO.lw(bt, w), w, bk, er)), N.le_refl(1n+ST.bdeg(bt)))
    case False{} False{}:
      +h30 = NO.h30_of(bt, hr, er)
      +e = Equal.trans(Nat, ST.bdeg(BO.bput(BO.bgrow(bt), NO.lw(bt, w), w)), 1n+ST.bdeg(BO.bgrow(bt)), 1n+ST.bdeg(bt),
        BO.put_deg(BO.bgrow(bt), NO.lw(bt, w), w, BO.grow_ok(bt, bk, h30), NO.grow_room(bt, bk, h30)),
        Equal.cong(Nat, Nat, z => 1n+z, ST.bdeg(BO.bgrow(bt)), ST.bdeg(bt), BO.grow_deg(bt, bk)))
      L.subst(Nat, z => {Nat.is_le(z, 1n+ST.bdeg(bt)) == True{} : Bool}, 1n+ST.bdeg(bt), ST.bdeg(BO.bput(BO.bgrow(bt), NO.lw(bt, w), w)), Equal.sym(Nat, ST.bdeg(BO.bput(BO.bgrow(bt), NO.lw(bt, w), w)), 1n+ST.bdeg(bt), e), N.le_refl(1n+ST.bdeg(bt)))

# mu grows by at most one when the maximum degree does.
def mu_le1(+d1: Bool, +d2: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +at2: AR.Tree<AR.Tree<U32>>, +hm: {Nat.is_le(GT.mdeg(RM.BW(lo, hi, at2)), 1n+GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}) -> {Nat.is_le(GT.mu(ST.Sh{d2, lo, hi, depth, it, at2}), Nat.add(GT.mu(ST.Sh{d1, lo, hi, depth, it, at}), 1n)) == True{} : Bool}:
  +s = Nat.sub(hi, lo)
  +md = GT.mdeg(RM.BW(lo, hi, at))
  N.le_trans(GT.mu(ST.Sh{d2, lo, hi, depth, it, at2}), Nat.add(s, 1n+md), Nat.add(Nat.add(s, md), 1n),
    W.add_mono(s, GT.mdeg(RM.BW(lo, hi, at2)), 1n+md, hm),
    L.subst(Nat, z => {Nat.is_le(Nat.add(s, 1n+md), z) == True{} : Bool}, 1n+Nat.add(s, md), Nat.add(Nat.add(s, md), 1n), Equal.sym(Nat, Nat.add(Nat.add(s, md), 1n), 1n+Nat.add(s, md), N.add_comm(Nat.add(s, md), 1n)),
      L.subst(Nat, z => {Nat.is_le(Nat.add(s, 1n+md), z) == True{} : Bool}, Nat.add(s, 1n+md), 1n+Nat.add(s, md), N.add_succ(s, md), N.le_refl(Nat.add(s, 1n+md)))))

# ---- per-vertex facts under the room premise ----

def deg_x(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32) -> {Nat.is_le(ST.bdeg(RM.BX(dir, lo, hi, depth, it, at, x)), GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}:
  mdeg_nth(RM.BW(lo, hi, at), RM.LX(lo, hi, it, x))

def mdeg_mu(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> {Nat.is_le(GT.mdeg(RM.BW(lo, hi, at)), GT.mu(ST.Sh{dir, lo, hi, depth, it, at})) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(GT.mdeg(RM.BW(lo, hi, at)), z) == True{} : Bool}, Nat.add(GT.mdeg(RM.BW(lo, hi, at)), Nat.sub(hi, lo)), GT.mu(ST.Sh{dir, lo, hi, depth, it, at}), N.add_comm(GT.mdeg(RM.BW(lo, hi, at)), Nat.sub(hi, lo)),
    N.le_add_right(GT.mdeg(RM.BW(lo, hi, at)), Nat.sub(hi, lo)))

def room_x(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hx: {RM.FX(lo, hi, it, x) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, x)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, x)), 30n)) == True{} : Bool}:
  room_of(RM.BX(dir, lo, hi, depth, it, at, x), RM.fx_bk(dir, lo, hi, depth, it, at, x, h, hx), GT.mu(ST.Sh{dir, lo, hi, depth, it, at}), q, hq, N.le_trans(ST.bdeg(RM.BX(dir, lo, hi, depth, it, at, x)), GT.mdeg(RM.BW(lo, hi, at)), GT.mu(ST.Sh{dir, lo, hi, depth, it, at}), deg_x(dir, lo, hi, depth, it, at, x), mdeg_mu(dir, lo, hi, depth, it, at)), hroom)

# ---- the first update (the block of u) ----

def A1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<U32>:
  NO.asel(RM.BX(dir, lo, hi, depth, it, at, u), v, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, u), v), NO.room(RM.BX(dir, lo, hi, depth, it, at, u)))

def AT1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(RM.IX(lo, hi, it, u)), A1(dir, lo, hi, depth, it, at, u, v))

def BW1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.update(AR.Tree<U32>, RM.BW(lo, hi, at), W.lbu(u, RM.KS(lo, hi, it)), A1(dir, lo, hi, depth, it, at, u, v))

def at1_perfect(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, depth, AT1(dir, lo, hi, depth, it, at, u, v)) == True{} : Bool}:
  AR.upd_perfect(AR.Tree<U32>, depth, at, U32.to_nat(RM.IX(lo, hi, it, u)), A1(dir, lo, hi, depth, it, at, u, v), OP.g_adj(dir, lo, hi, depth, it, at, h))

def bw1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}) -> {RM.BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)) == BW1(dir, lo, hi, depth, it, at, u, v) : List<&2, AR.Tree<U32>>}:
  RM.win_after(lo, hi, depth, it, at, u, A1(dir, lo, hi, depth, it, at, u, v), OP.g_adj(dir, lo, hi, depth, it, at, h), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, u, h, RM.fx_hin(dir, lo, hi, depth, it, at, u, hu)), ED.slot_nat(dir, lo, hi, depth, it, at, u, h, RM.fx_hin(dir, lo, hi, depth, it, at, u, hu)))

def am1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hr: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}) -> {ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v)) == GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v)), GS.put(u, ST.uset(ST.bents(A1(dir, lo, hi, depth, it, at, u, v))), RM.AM(lo, hi, it, at)), GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)),
    EO.put_model(RM.KS(lo, hi, it), RM.BW(lo, hi, at), u, A1(dir, lo, hi, depth, it, at, u, v), RM.hlen_of(dir, lo, hi, depth, it, at, h), RM.fx_eq(dir, lo, hi, depth, it, at, u, h, hu)),
    Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(u, z, RM.AM(lo, hi, it, at)), ST.uset(ST.bents(A1(dir, lo, hi, depth, it, at, u, v))), GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)),
      NO.asem(RM.BX(dir, lo, hi, depth, it, at, u), v, RM.fx_bk(dir, lo, hi, depth, it, at, u, h, hu), hr, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, u), v), {==}, NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), {==})))

def blocks1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hr: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}) -> {ST.blocks_ok(BW1(dir, lo, hi, depth, it, at, u, v)) == True{} : Bool}:
  EO.blocks_update(RM.BW(lo, hi, at), W.lbu(u, RM.KS(lo, hi, it)), A1(dir, lo, hi, depth, it, at, u, v), OP.g_blocks(dir, lo, hi, depth, it, at, h), NO.asel_ok(RM.BX(dir, lo, hi, depth, it, at, u), v, RM.fx_bk(dir, lo, hi, depth, it, at, u, h, hu), hr, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, u), v), {==}, NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), {==}))

def mdeg1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hr: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(BW1(dir, lo, hi, depth, it, at, u, v)), 1n+GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}:
  mdeg_upd_bound(RM.BW(lo, hi, at), W.lbu(u, RM.KS(lo, hi, it)), A1(dir, lo, hi, depth, it, at, u, v), 1n+GT.mdeg(RM.BW(lo, hi, at)),
    N.le_trans(ST.bdeg(A1(dir, lo, hi, depth, it, at, u, v)), 1n+ST.bdeg(RM.BX(dir, lo, hi, depth, it, at, u)), 1n+GT.mdeg(RM.BW(lo, hi, at)), asel_deg(RM.BX(dir, lo, hi, depth, it, at, u), v, RM.fx_bk(dir, lo, hi, depth, it, at, u, h, hu), hr, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, u), v), NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), {==}), deg_x(dir, lo, hi, depth, it, at, u)),
    N.le_succ(GT.mdeg(RM.BW(lo, hi, at))))

# ---- the second update (undirected graphs; the block of v) ----

def A2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<U32>:
  NO.asel(RM.BX(dir, lo, hi, depth, it, at, v), u, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, v), u), NO.room(RM.BX(dir, lo, hi, depth, it, at, v)))

def AT2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, depth, AT1(dir, lo, hi, depth, it, at, u, v), U32.to_nat(RM.IX(lo, hi, it, v)), A2(dir, lo, hi, depth, it, at, u, v))

def BW2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, RM.KS(lo, hi, it)), A2(dir, lo, hi, depth, it, at, u, v))

def hx2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}) -> {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT1(dir, lo, hi, depth, it, at, u, v)), U32.to_nat(RM.IX(lo, hi, it, v))) == Some{RM.BX(dir, lo, hi, depth, it, at, v)} : Maybe<&2, AR.Tree<U32>>}:
  Equal.trans(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT1(dir, lo, hi, depth, it, at, u, v)), U32.to_nat(RM.IX(lo, hi, it, v))), SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(RM.IX(lo, hi, it, v))), Some{RM.BX(dir, lo, hi, depth, it, at, v)},
    EO.tree_other(depth, at, U32.to_nat(RM.IX(lo, hi, it, u)), A1(dir, lo, hi, depth, it, at, u, v), U32.to_nat(RM.IX(lo, hi, it, v)), RM.fx_hi(dir, lo, hi, depth, it, at, u, h, hu), OP.g_adj(dir, lo, hi, depth, it, at, h), RM.sne(dir, lo, hi, depth, it, at, u, v, h, hu, hv, huv)),
    RM.fx_hx(dir, lo, hi, depth, it, at, v, h, hv))

def bw2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {RM.BW(lo, hi, AT2(dir, lo, hi, depth, it, at, u, v)) == BW2(dir, lo, hi, depth, it, at, u, v) : List<&2, AR.Tree<U32>>}:
  Equal.trans(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, AT2(dir, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, RM.BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)), W.lbu(v, RM.KS(lo, hi, it)), A2(dir, lo, hi, depth, it, at, u, v)), BW2(dir, lo, hi, depth, it, at, u, v),
    RM.win_after(lo, hi, depth, it, AT1(dir, lo, hi, depth, it, at, u, v), v, A2(dir, lo, hi, depth, it, at, u, v), at1_perfect(dir, lo, hi, depth, it, at, u, v, h), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, v, h, RM.fx_hin(dir, lo, hi, depth, it, at, v, hv)), ED.slot_nat(dir, lo, hi, depth, it, at, v, h, RM.fx_hin(dir, lo, hi, depth, it, at, v, hv))),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, W.lbu(v, RM.KS(lo, hi, it)), A2(dir, lo, hi, depth, it, at, u, v)), RM.BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)), BW1(dir, lo, hi, depth, it, at, u, v), bw1(dir, lo, hi, depth, it, at, u, v, h, hu)))

def am2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +hru: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}, +hrv: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, v)), 30n)) == True{} : Bool}) -> {ST.amodel(RM.KS(lo, hi, it), BW2(dir, lo, hi, depth, it, at, u, v)) == GS.put(v, GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +hlen = Equal.trans(Nat, SC.length(U32, RM.KS(lo, hi, it)), SC.length(AR.Tree<U32>, RM.BW(lo, hi, at)), SC.length(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v)), RM.hlen_of(dir, lo, hi, depth, it, at, h), Equal.sym(Nat, SC.length(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v)), SC.length(AR.Tree<U32>, RM.BW(lo, hi, at)), LL.length_update(AR.Tree<U32>, RM.BW(lo, hi, at), W.lbu(u, RM.KS(lo, hi, it)), A1(dir, lo, hi, depth, it, at, u, v))))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(RM.KS(lo, hi, it), BW2(dir, lo, hi, depth, it, at, u, v)), GS.put(v, ST.uset(ST.bents(A2(dir, lo, hi, depth, it, at, u, v))), ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))),
    EO.put_model(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v), v, A2(dir, lo, hi, depth, it, at, u, v), hlen, RM.fx_eq(dir, lo, hi, depth, it, at, v, h, hv)),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.put(v, ST.uset(ST.bents(A2(dir, lo, hi, depth, it, at, u, v))), ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)), ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))),
      Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(v, z, ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), ST.uset(ST.bents(A2(dir, lo, hi, depth, it, at, u, v))), GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)),
        NO.asem(RM.BX(dir, lo, hi, depth, it, at, v), u, RM.fx_bk(dir, lo, hi, depth, it, at, v, h, hv), hrv, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, v), u), {==}, NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), {==})),
      Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(v, GS.sadd(u, RM.SX(dir, lo, hi, depth, it, at, v)), z), ST.amodel(RM.KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v)), GS.put(u, GS.sadd(v, RM.SX(dir, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)), am1(dir, lo, hi, depth, it, at, u, v, h, hu, hru))))

def blocks2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +hru: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}, +hrv: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, v)), 30n)) == True{} : Bool}) -> {ST.blocks_ok(BW2(dir, lo, hi, depth, it, at, u, v)) == True{} : Bool}:
  EO.blocks_update(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, RM.KS(lo, hi, it)), A2(dir, lo, hi, depth, it, at, u, v), blocks1(dir, lo, hi, depth, it, at, u, v, h, hu, hru), NO.asel_ok(RM.BX(dir, lo, hi, depth, it, at, v), u, RM.fx_bk(dir, lo, hi, depth, it, at, v, h, hv), hrv, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, v), u), {==}, NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), {==}))

def mdeg2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +hru: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, u)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, u)), 30n)) == True{} : Bool}, +hrv: {Bool.or(NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), Nat.is_le(ST.blcap(RM.BX(dir, lo, hi, depth, it, at, v)), 30n)) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(BW2(dir, lo, hi, depth, it, at, u, v)), 1n+GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}:
  mdeg_upd_bound(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, RM.KS(lo, hi, it)), A2(dir, lo, hi, depth, it, at, u, v), 1n+GT.mdeg(RM.BW(lo, hi, at)),
    N.le_trans(ST.bdeg(A2(dir, lo, hi, depth, it, at, u, v)), 1n+ST.bdeg(RM.BX(dir, lo, hi, depth, it, at, v)), 1n+GT.mdeg(RM.BW(lo, hi, at)), asel_deg(RM.BX(dir, lo, hi, depth, it, at, v), u, RM.fx_bk(dir, lo, hi, depth, it, at, v, h, hv), hrv, NO.fnd(RM.BX(dir, lo, hi, depth, it, at, v), u), NO.room(RM.BX(dir, lo, hi, depth, it, at, v)), {==}), deg_x(dir, lo, hi, depth, it, at, v)),
    mdeg1(dir, lo, hi, depth, it, at, u, v, h, hu, hru))

# The specification's step when both vertices exist and u != v.
def spec_add(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}) -> {GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddEdge{u, v}) == (GS.GM{dir, GS.link(dir, RM.AM(lo, hi, it, at), u, v, RM.SX(dir, lo, hi, depth, it, at, u), RM.SX(dir, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}:
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, RM.AM(lo, hi, it, at)), Some{RM.SX(dir, lo, hi, depth, it, at, u)}, RM.fx_find(dir, lo, hi, depth, it, at, u, h, hu)) : {GS.add_edge_at(_, GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v) == (GS.GM{dir, GS.link(dir, RM.AM(lo, hi, it, at), u, v, RM.SX(dir, lo, hi, depth, it, at, u), RM.SX(dir, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), Some{RM.SX(dir, lo, hi, depth, it, at, v)}, RM.fx_find(dir, lo, hi, depth, it, at, v, h, hv)) : {GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, _, GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v) == (GS.GM{dir, GS.link(dir, RM.AM(lo, hi, it, at), u, v, RM.SX(dir, lo, hi, depth, it, at, u), RM.SX(dir, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  %Equal.sym(Bool, GS.same(u, v), False{}, huv) : {GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, Some{RM.SX(dir, lo, hi, depth, it, at, v)}, _, dir, RM.AM(lo, hi, it, at), u, v) == (GS.GM{dir, GS.link(dir, RM.AM(lo, hi, it, at), u, v, RM.SX(dir, lo, hi, depth, it, at, u), RM.SX(dir, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  {==}

# ---- add_edge: the successful branches ----

def ae_t(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{True{}, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{True{}, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> UC.UCore(ST.Sh{True{}, lo, hi, depth, it, at}, G.ae_loop(True{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(True{}, lo, hi, depth, it, at, u)}, Some{RM.SX(True{}, lo, hi, depth, it, at, v)}, False{}, True{}, RM.AM(lo, hi, it, at), u, v), 1n):
  +hru = room_x(True{}, lo, hi, depth, it, at, u, h, hu, q, hq, hroom)
  +e1 = Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(True{}, lo, hi, depth, AR.thaw(U32, it), z), G.add_nbr(A2.thaw2(at), RM.IX(lo, hi, it, u), v), A2.thaw2(AT1(True{}, lo, hi, depth, it, at, u, v)),
    NO.add_nbr_ok(depth, at, RM.IX(lo, hi, it, u), RM.BX(True{}, lo, hi, depth, it, at, u), v, ED.dep32(True{}, lo, hi, depth, it, at, h), RM.fx_hi(True{}, lo, hi, depth, it, at, u, h, hu), RM.fx_hx(True{}, lo, hi, depth, it, at, u, h, hu), OP.g_adj(True{}, lo, hi, depth, it, at, h), RM.fx_bk(True{}, lo, hi, depth, it, at, u, h, hu), hru))
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(True{}, z), ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v))), GS.put(u, GS.sadd(v, RM.SX(True{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v))), ST.amodel(RM.KS(lo, hi, it), BW1(True{}, lo, hi, depth, it, at, u, v)), GS.put(u, GS.sadd(v, RM.SX(True{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(RM.KS(lo, hi, it), z), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)),
      am1(True{}, lo, hi, depth, it, at, u, v, h, hu, hru)))
  +wf = GT.wf_after(True{}, lo, hi, depth, it, at, h, E.AddEdge{u, v}, GS.GM{True{}, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{True{}, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}}), (GS.GM{True{}, GS.put(u, GS.sadd(v, RM.SX(True{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{True{}, lo, hi, depth, it, at}), E.AddEdge{u, v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{True{}, lo, hi, depth, it, at}), E.AddEdge{u, v}), (GS.GM{True{}, GS.link(True{}, RM.AM(lo, hi, it, at), u, v, RM.SX(True{}, lo, hi, depth, it, at, u), RM.SX(True{}, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}), spec_add(True{}, lo, hi, depth, it, at, u, v, h, hu, hv, huv))))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, BW1(True{}, lo, hi, depth, it, at, u, v), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)), blocks1(True{}, lo, hi, depth, it, at, u, v, h, hu, hru))
  +hm = L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(z), 1n+GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}, BW1(True{}, lo, hi, depth, it, at, u, v), RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)), mdeg1(True{}, lo, hi, depth, it, at, u, v, h, hu, hru))
  UC.uc_mk(ST.Sh{True{}, lo, hi, depth, it, at}, G.ae_loop(True{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(True{}, lo, hi, depth, it, at, u)}, Some{RM.SX(True{}, lo, hi, depth, it, at, v)}, False{}, True{}, RM.AM(lo, hi, it, at), u, v), 1n,
    ST.Sh{True{}, lo, hi, depth, it, AT1(True{}, lo, hi, depth, it, at, u, v)}, Done{Unit{}}, e1,
    GT.good_mk(True{}, lo, hi, depth, it, AT1(True{}, lo, hi, depth, it, at, u, v), OP.g_depth(True{}, lo, hi, depth, it, at, h), OP.g_ids(True{}, lo, hi, depth, it, at, h), at1_perfect(True{}, lo, hi, depth, it, at, u, v, h), OP.g_lohi(True{}, lo, hi, depth, it, at, h), OP.g_cap(True{}, lo, hi, depth, it, at, h), OP.g_asc(True{}, lo, hi, depth, it, at, h), hbl, wf),
    e3, mu_le1(True{}, True{}, lo, hi, depth, it, at, AT1(True{}, lo, hi, depth, it, at, u, v), hm))

def ae_f(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{False{}, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{False{}, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> UC.UCore(ST.Sh{False{}, lo, hi, depth, it, at}, G.ae_loop(False{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(False{}, lo, hi, depth, it, at, u)}, Some{RM.SX(False{}, lo, hi, depth, it, at, v)}, False{}, False{}, RM.AM(lo, hi, it, at), u, v), 1n):
  +hru = room_x(False{}, lo, hi, depth, it, at, u, h, hu, q, hq, hroom)
  +hrv = room_x(False{}, lo, hi, depth, it, at, v, h, hv, q, hq, hroom)
  +e1 = Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(False{}, lo, hi, depth, AR.thaw(U32, it), z), G.add_nbr(G.add_nbr(A2.thaw2(at), RM.IX(lo, hi, it, u), v), RM.IX(lo, hi, it, v), u), A2.thaw2(AT2(False{}, lo, hi, depth, it, at, u, v)),
    Equal.trans(Array<Array<U32>>, G.add_nbr(G.add_nbr(A2.thaw2(at), RM.IX(lo, hi, it, u), v), RM.IX(lo, hi, it, v), u), G.add_nbr(A2.thaw2(AT1(False{}, lo, hi, depth, it, at, u, v)), RM.IX(lo, hi, it, v), u), A2.thaw2(AT2(False{}, lo, hi, depth, it, at, u, v)),
      Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => G.add_nbr(z, RM.IX(lo, hi, it, v), u), G.add_nbr(A2.thaw2(at), RM.IX(lo, hi, it, u), v), A2.thaw2(AT1(False{}, lo, hi, depth, it, at, u, v)),
        NO.add_nbr_ok(depth, at, RM.IX(lo, hi, it, u), RM.BX(False{}, lo, hi, depth, it, at, u), v, ED.dep32(False{}, lo, hi, depth, it, at, h), RM.fx_hi(False{}, lo, hi, depth, it, at, u, h, hu), RM.fx_hx(False{}, lo, hi, depth, it, at, u, h, hu), OP.g_adj(False{}, lo, hi, depth, it, at, h), RM.fx_bk(False{}, lo, hi, depth, it, at, u, h, hu), hru)),
      NO.add_nbr_ok(depth, AT1(False{}, lo, hi, depth, it, at, u, v), RM.IX(lo, hi, it, v), RM.BX(False{}, lo, hi, depth, it, at, v), u, ED.dep32(False{}, lo, hi, depth, it, at, h), RM.fx_hi(False{}, lo, hi, depth, it, at, v, h, hv), hx2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, huv), at1_perfect(False{}, lo, hi, depth, it, at, u, v, h), RM.fx_bk(False{}, lo, hi, depth, it, at, v, h, hv), hrv)))
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(False{}, z), ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sadd(u, RM.SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(False{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v))), ST.amodel(RM.KS(lo, hi, it), BW2(False{}, lo, hi, depth, it, at, u, v)), GS.put(v, GS.sadd(u, RM.SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(False{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at))),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(RM.KS(lo, hi, it), z), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), BW2(False{}, lo, hi, depth, it, at, u, v), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)),
      am2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, hru, hrv)))
  +wf = GT.wf_after(False{}, lo, hi, depth, it, at, h, E.AddEdge{u, v}, GS.GM{False{}, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{False{}, ST.amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}}), (GS.GM{False{}, GS.put(v, GS.sadd(u, RM.SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sadd(v, RM.SX(False{}, lo, hi, depth, it, at, u)), RM.AM(lo, hi, it, at)))}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{False{}, lo, hi, depth, it, at}), E.AddEdge{u, v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{False{}, lo, hi, depth, it, at}), E.AddEdge{u, v}), (GS.GM{False{}, GS.link(False{}, RM.AM(lo, hi, it, at), u, v, RM.SX(False{}, lo, hi, depth, it, at, u), RM.SX(False{}, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}), spec_add(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, huv))))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, BW2(False{}, lo, hi, depth, it, at, u, v), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), BW2(False{}, lo, hi, depth, it, at, u, v), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)), blocks2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, hru, hrv))
  +hm = L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(z), 1n+GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}, BW2(False{}, lo, hi, depth, it, at, u, v), RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), BW2(False{}, lo, hi, depth, it, at, u, v), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)), mdeg2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, hru, hrv))
  +hpa = AR.upd_perfect(AR.Tree<U32>, depth, AT1(False{}, lo, hi, depth, it, at, u, v), U32.to_nat(RM.IX(lo, hi, it, v)), A2(False{}, lo, hi, depth, it, at, u, v), at1_perfect(False{}, lo, hi, depth, it, at, u, v, h))
  UC.uc_mk(ST.Sh{False{}, lo, hi, depth, it, at}, G.ae_loop(False{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(False{}, lo, hi, depth, it, at, u)}, Some{RM.SX(False{}, lo, hi, depth, it, at, v)}, False{}, False{}, RM.AM(lo, hi, it, at), u, v), 1n,
    ST.Sh{False{}, lo, hi, depth, it, AT2(False{}, lo, hi, depth, it, at, u, v)}, Done{Unit{}}, e1,
    GT.good_mk(False{}, lo, hi, depth, it, AT2(False{}, lo, hi, depth, it, at, u, v), OP.g_depth(False{}, lo, hi, depth, it, at, h), OP.g_ids(False{}, lo, hi, depth, it, at, h), hpa, OP.g_lohi(False{}, lo, hi, depth, it, at, h), OP.g_cap(False{}, lo, hi, depth, it, at, h), OP.g_asc(False{}, lo, hi, depth, it, at, h), hbl, wf),
    e3, mu_le1(False{}, False{}, lo, hi, depth, it, at, AT2(False{}, lo, hi, depth, it, at, u, v), hm))

def ae_dir(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_loop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, Some{RM.SX(dir, lo, hi, depth, it, at, v)}, False{}, dir, RM.AM(lo, hi, it, at), u, v), 1n):
  match dir:
    case True{}:
      ae_t(lo, hi, depth, it, at, u, v, h, hu, hv, huv, q, hq, hroom)
    case False{}:
      ae_f(lo, hi, depth, it, at, u, v, h, hu, hv, huv, q, hq, hroom)

# ---- add_edge: the case analysis ----

def ae_case3(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +hv: {RM.FX(lo, hi, it, v) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, same: Bool, +es: {U32.is_eq(u, v) == same : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_loop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, same), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, Some{RM.SX(dir, lo, hi, depth, it, at, v)}, same, dir, RM.AM(lo, hi, it, at), u, v), 1n):
  match same:
    case True{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.ae_loop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, True{}), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, Some{RM.SX(dir, lo, hi, depth, it, at, v)}, True{}, dir, RM.AM(lo, hi, it, at), u, v), 1n, E.SelfLoop{}, {==}, {==})
    case False{}:
      ae_dir(dir, lo, hi, depth, it, at, u, v, h, hu, hv, es, q, hq, hroom)

def ae_case2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {RM.FX(lo, hi, it, u) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, fv: Bool, +efv: {RM.FX(lo, hi, it, v) == fv : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, fv), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, RM.SX(dir, lo, hi, depth, it, at, v)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n):
  match fv:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.ae_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, False{}), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, LB.pickv(List<&2, BE.Entry<U32, Unit>>, False{}, RM.SX(dir, lo, hi, depth, it, at, v)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n, E.VertexNotFound{}, {==}, {==})
    case True{}:
      ae_case3(dir, lo, hi, depth, it, at, u, v, h, hu, efv, q, hq, hroom, U32.is_eq(u, v), {==})

def ae_case1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, fu: Bool, +efu: {RM.FX(lo, hi, it, u) == fu : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), u, v, fu), GS.add_edge_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, fu, RM.SX(dir, lo, hi, depth, it, at, u)), GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n):
  match fu:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.ae_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), u, v, False{}), GS.add_edge_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, False{}, RM.SX(dir, lo, hi, depth, it, at, u)), GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n, E.VertexNotFound{}, {==}, {==})
    case True{}:
      L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_v(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), RM.IX(lo, hi, it, u), u, v, z), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n),
        G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
        Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)),
        L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), RM.IX(lo, hi, it, v), u, v, RM.FX(lo, hi, it, v)), GS.add_edge_at(Some{RM.SX(dir, lo, hi, depth, it, at, u)}, m, GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n),
          LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), GS.find(v, RM.AM(lo, hi, it, at)),
          Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), ED.gfind(dir, lo, hi, depth, it, at, v, h)),
          ae_case2(dir, lo, hi, depth, it, at, u, v, h, efu, q, hq, hroom, RM.FX(lo, hi, it, v), {==})))

def ae_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.add_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddEdge{u, v}), 1n):
  L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_u(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), u, v, z), GS.add_edge_at(GS.find(u, RM.AM(lo, hi, it, at)), GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n),
    G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, u), RM.FX(lo, hi, it, u)}, G.locate(depth, u, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
    Equal.sym(G.Loc, G.locate(depth, u, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, u), RM.FX(lo, hi, it, u)}, OP.hv_locate(dir, lo, hi, depth, it, at, u, h)),
    L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.ae_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, u), u, v, RM.FX(lo, hi, it, u)), GS.add_edge_at(m, GS.find(v, RM.AM(lo, hi, it, at)), GS.same(u, v), dir, RM.AM(lo, hi, it, at), u, v), 1n),
      LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, u), RM.SX(dir, lo, hi, depth, it, at, u)), GS.find(u, RM.AM(lo, hi, it, at)),
      Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, RM.AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, u), RM.SX(dir, lo, hi, depth, it, at, u)), ED.gfind(dir, lo, hi, depth, it, at, u, h)),
      ae_case1(dir, lo, hi, depth, it, at, u, v, h, q, hq, hroom, RM.FX(lo, hi, it, u), {==})))

# add_edge refines the specification, preserves the invariant and raises the measure by at most one.
def so_add_edge(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> GT.StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.AddEdge{u, v}):
  UC.uc_step(ST.Sh{dir, lo, hi, depth, it, at}, E.AddEdge{u, v}, G.add_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v), ae_core(dir, lo, hi, depth, it, at, u, v, h, q, hq, hroom), {==})
