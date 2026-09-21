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

# ---- shorthand for the pieces of a good shadow ----

def KS(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>) -> List<&2, U32>:
  ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo))

def BW(+lo: Nat, +hi: Nat, +at: AR.Tree<AR.Tree<U32>>) -> List<&2, AR.Tree<U32>>:
  ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))

def AM(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>:
  ST.amodel(KS(lo, hi, it), BW(lo, hi, at))

def IX(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +x: U32) -> U32:
  U32.from_nat(OP.lbv(lo, hi, it, x))

def FX(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +x: U32) -> Bool:
  SE.found_of(it, OP.lbv(lo, hi, it, x), hi, x)

def BX(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32) -> AR.Tree<U32>:
  ED.blk_of(dir, lo, hi, depth, it, at, x)

def SX(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32) -> List<&2, BE.Entry<U32, Unit>>:
  ST.uset(ST.bents(BX(dir, lo, hi, depth, it, at, x)))

def LX(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +x: U32) -> Nat:
  W.lbs(x, AR.slots(U32, it), Nat.sub(hi, lo), lo)

# ---- facts about a present vertex ----

def fx_hin(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}:
  ED.found_lt(it, OP.lbv(lo, hi, it, x), hi, x, Nat.is_lt(OP.lbv(lo, hi, it, x), hi), {==}, hf)

def fx_hi(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(IX(lo, hi, it, x)), SC.pow2(depth)) == True{} : Bool}:
  +hin = fx_hin(dir, lo, hi, depth, it, at, x, hf)
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, OP.lbv(lo, hi, it, x), U32.to_nat(IX(lo, hi, it, x)), Equal.sym(Nat, U32.to_nat(IX(lo, hi, it, x)), OP.lbv(lo, hi, it, x), ED.slot_nat(dir, lo, hi, depth, it, at, x, h, hin)), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, x, h, hin))

def fx_hx(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(IX(lo, hi, it, x))) == Some{BX(dir, lo, hi, depth, it, at, x)} : Maybe<&2, AR.Tree<U32>>}:
  ED.blk_at(dir, lo, hi, depth, it, at, x, h, fx_hin(dir, lo, hi, depth, it, at, x, hf))

def fx_bk(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {ST.blk_ok(BX(dir, lo, hi, depth, it, at, x)) == True{} : Bool}:
  ED.blk_ok_of(dir, lo, hi, depth, it, at, x, h, fx_hin(dir, lo, hi, depth, it, at, x, hf))

def fx_find(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {GS.find(x, AM(lo, hi, it, at)) == Some{SX(dir, lo, hi, depth, it, at, x)} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  L.subst(Bool, b => {GS.find(x, AM(lo, hi, it, at)) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, b, SX(dir, lo, hi, depth, it, at, x)) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, FX(lo, hi, it, x), True{}, hf,
    ED.gfind(dir, lo, hi, depth, it, at, x, h))

def fx_eq(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {FX(lo, hi, it, x) == True{} : Bool}) -> {LB.eq_at(KS(lo, hi, it), W.lbu(x, KS(lo, hi, it)), x) == True{} : Bool}:
  +k = Nat.sub(hi, lo)
  +xs = AR.slots(U32, it)
  +l = LX(lo, hi, it, x)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hlen = L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(depth), AR.slots_length(U32, depth, it, OP.g_ids(dir, lo, hi, depth, it, at, h))), OP.g_cap(dir, lo, hi, depth, it, at, h))
  +hw = Equal.trans(Bool, W.eq_at(KS(lo, hi, it), l, x), SE.found_of(it, Nat.add(lo, l), hi, x), True{},
    Equal.sym(Bool, SE.found_of(it, Nat.add(lo, l), hi, x), W.eq_at(KS(lo, hi, it), l, x), W.found_bridge(it, lo, hi, k, l, x, {==}, hlo, W.lbs_le(x, xs, k, lo), hlen)),
    hf)
  +hl = Equal.trans(Bool, LB.eq_at(KS(lo, hi, it), l, x), W.eq_at(KS(lo, hi, it), l, x), True{}, W.eqm_same(SC.nth(U32, KS(lo, hi, it), l), x), hw)
  L.subst(Nat, z => {LB.eq_at(KS(lo, hi, it), z, x) == True{} : Bool}, l, W.lbu(x, KS(lo, hi, it)), W.lbs_lbu(x, xs, k, lo), hl)

# ---- replacing the block of a present vertex ----

def win_after(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +arr: AR.Tree<AR.Tree<U32>>, +x: U32, +b: AR.Tree<U32>, +pf: {AR.perfect(AR.Tree<U32>, depth, arr) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), SC.pow2(depth)) == True{} : Bool}, +es: {U32.to_nat(IX(lo, hi, it, x)) == OP.lbv(lo, hi, it, x) : Nat}) -> {BW(lo, hi, AR.upd(AR.Tree<U32>, depth, arr, U32.to_nat(IX(lo, hi, it, x)), b)) == SC.update(AR.Tree<U32>, BW(lo, hi, arr), W.lbu(x, KS(lo, hi, it)), b) : List<&2, AR.Tree<U32>>}:
  +l = LX(lo, hi, it, x)
  Equal.trans(List<&2, AR.Tree<U32>>, BW(lo, hi, AR.upd(AR.Tree<U32>, depth, arr, U32.to_nat(IX(lo, hi, it, x)), b)), BW(lo, hi, AR.upd(AR.Tree<U32>, depth, arr, Nat.add(lo, l), b)), SC.update(AR.Tree<U32>, BW(lo, hi, arr), W.lbu(x, KS(lo, hi, it)), b),
    Equal.cong(Nat, List<&2, AR.Tree<U32>>, z => BW(lo, hi, AR.upd(AR.Tree<U32>, depth, arr, z, b)), U32.to_nat(IX(lo, hi, it, x)), Nat.add(lo, l), es),
    Equal.trans(List<&2, AR.Tree<U32>>, BW(lo, hi, AR.upd(AR.Tree<U32>, depth, arr, Nat.add(lo, l), b)), SC.update(AR.Tree<U32>, BW(lo, hi, arr), l, b), SC.update(AR.Tree<U32>, BW(lo, hi, arr), W.lbu(x, KS(lo, hi, it)), b),
      EO.win_upd_tree(depth, arr, lo, Nat.sub(hi, lo), l, b, hin, pf),
      Equal.cong(Nat, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, BW(lo, hi, arr), z, b), l, W.lbu(x, KS(lo, hi, it)), W.lbs_lbu(x, AR.slots(U32, it), Nat.sub(hi, lo), lo))))

def bnth_lbu(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32) -> {ED.bnth(BW(lo, hi, at), W.lbu(x, KS(lo, hi, it))) == BX(dir, lo, hi, depth, it, at, x) : AR.Tree<U32>}:
  Equal.cong(Nat, AR.Tree<U32>, z => ED.bnth(BW(lo, hi, at), z), W.lbu(x, KS(lo, hi, it)), LX(lo, hi, it, x), Equal.sym(Nat, LX(lo, hi, it, x), W.lbu(x, KS(lo, hi, it)), W.lbs_lbu(x, AR.slots(U32, it), Nat.sub(hi, lo), lo)))

def bnth_upd_other(+bs: List<&2, AR.Tree<U32>>, +l: Nat, +b: AR.Tree<U32>, +i: Nat, +hne: {Nat.is_eq(l, i) == False{} : Bool}) -> {ED.bnth(SC.update(AR.Tree<U32>, bs, l, b), i) == ED.bnth(bs, i) : AR.Tree<U32>}:
  Equal.cong(Maybe<&2, AR.Tree<U32>>, AR.Tree<U32>, m => L.some_value(AR.Tree<U32>, m, BK.leaf0()), SC.nth(AR.Tree<U32>, SC.update(AR.Tree<U32>, bs, l, b), i), SC.nth(AR.Tree<U32>, bs, i), LL.nth_update_other(AR.Tree<U32>, bs, l, i, b, hne))

def dsel_deg(+bt: AR.Tree<U32>, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, f: Bool, +ef: {NO.fnd(bt, w) == f : Bool}) -> {Nat.is_le(ST.bdeg(NO.dsel(bt, w, f)), ST.bdeg(bt)) == True{} : Bool}:
  match f:
    case True{}:
      L.subst(Nat, z => {Nat.is_le(z, ST.bdeg(bt)) == True{} : Bool}, Nat.sub(ST.bdeg(bt), 1n), ST.bdeg(BO.bdel(bt, NO.lw(bt, w))), Equal.sym(Nat, ST.bdeg(BO.bdel(bt, NO.lw(bt, w))), Nat.sub(ST.bdeg(bt), 1n), BO.del_deg(bt, NO.lw(bt, w), bk, NO.lw_lt(bt, w, ef))), H2.sub_le(ST.bdeg(bt), 1n))
    case False{}:
      N.le_refl(ST.bdeg(bt))

def is_eq_add(+lo: Nat, +a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(Nat.add(lo, a), Nat.add(lo, b)) == False{} : Bool}:
  match lo:
    case 0n:
      h
    case 1n+p:
      is_eq_add(p, a, b, h)

# The adjacency array after the first update (the block of u) and its window.
def AT1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, True{}))

def B1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<U32>:
  NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, True{})

def at1_perfect(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, depth, AT1(dir, lo, hi, depth, it, at, u, v)) == True{} : Bool}:
  AR.upd_perfect(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), B1(dir, lo, hi, depth, it, at, u, v), OP.g_adj(dir, lo, hi, depth, it, at, h))

def bw1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}) -> {BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)) == SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v)) : List<&2, AR.Tree<U32>>}:
  +hin = fx_hin(dir, lo, hi, depth, it, at, u, hu)
  win_after(lo, hi, depth, it, at, u, B1(dir, lo, hi, depth, it, at, u, v), OP.g_adj(dir, lo, hi, depth, it, at, h), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, u, h, hin), ED.slot_nat(dir, lo, hi, depth, it, at, u, h, hin))

def hlen_of(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(U32, KS(lo, hi, it)) == SC.length(AR.Tree<U32>, BW(lo, hi, at)) : Nat}:
  GT.hlen_good(dir, lo, hi, depth, it, at, h)

# model after the first update
def am1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {ST.amodel(KS(lo, hi, it), SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v))) == GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +b1 = B1(dir, lo, hi, depth, it, at, u, v)
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(KS(lo, hi, it), SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), b1)), GS.put(u, ST.uset(ST.bents(b1)), AM(lo, hi, it, at)), GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)),
    EO.put_model(KS(lo, hi, it), BW(lo, hi, at), u, b1, hlen_of(dir, lo, hi, depth, it, at, h), fx_eq(dir, lo, hi, depth, it, at, u, h, hu)),
    Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(u, z, AM(lo, hi, it, at)), ST.uset(ST.bents(b1)), GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)),
      NO.dsem(BX(dir, lo, hi, depth, it, at, u), v, fx_bk(dir, lo, hi, depth, it, at, u, h, hu), True{}, efb)))

def blocks1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {ST.blocks_ok(SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v))) == True{} : Bool}:
  EO.blocks_update(BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v), OP.g_blocks(dir, lo, hi, depth, it, at, h), NO.dsel_ok(BX(dir, lo, hi, depth, it, at, u), v, fx_bk(dir, lo, hi, depth, it, at, u, h, hu), True{}, efb))

def mdeg1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v))), GT.mdeg(BW(lo, hi, at))) == True{} : Bool}:
  GT.mdeg_upd_le(BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v),
    L.subst(AR.Tree<U32>, z => {Nat.is_le(ST.bdeg(B1(dir, lo, hi, depth, it, at, u, v)), ST.bdeg(z)) == True{} : Bool}, BX(dir, lo, hi, depth, it, at, u), ED.bnth(BW(lo, hi, at), W.lbu(u, KS(lo, hi, it))), Equal.sym(AR.Tree<U32>, ED.bnth(BW(lo, hi, at), W.lbu(u, KS(lo, hi, it))), BX(dir, lo, hi, depth, it, at, u), bnth_lbu(dir, lo, hi, depth, it, at, u)),
      dsel_deg(BX(dir, lo, hi, depth, it, at, u), v, fx_bk(dir, lo, hi, depth, it, at, u, h, hu), True{}, efb)))

# The specification's step when both vertices exist, u != v and u-v is an edge.
def spec_rm(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveEdge{u, v}) == (GS.GM{dir, GS.unlink(dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}:
  +su = SX(dir, lo, hi, depth, it, at, u)
  +sv = SX(dir, lo, hi, depth, it, at, v)
  +bu = BX(dir, lo, hi, depth, it, at, u)
  +esm = Equal.trans(Bool, GS.smem(v, su), NO.fnd(bu, v), True{}, Equal.sym(Bool, NO.fnd(bu, v), GS.smem(v, su), NO.e_is_some(bu, v, fx_bk(dir, lo, hi, depth, it, at, u, h, hu))), efb)
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, AM(lo, hi, it, at)), Some{su}, fx_find(dir, lo, hi, depth, it, at, u, h, hu)) : {GS.remove_edge_at(_, GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v) == (GS.GM{dir, GS.unlink(dir, AM(lo, hi, it, at), u, v, su, sv)}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, AM(lo, hi, it, at)), Some{sv}, fx_find(dir, lo, hi, depth, it, at, v, h, hv)) : {GS.remove_edge_at(Some{su}, _, dir, AM(lo, hi, it, at), u, v) == (GS.GM{dir, GS.unlink(dir, AM(lo, hi, it, at), u, v, su, sv)}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  %Equal.sym(Bool, GS.smem(v, su), True{}, esm) : {GS.remove_present(_, dir, AM(lo, hi, it, at), u, v, su, sv) == (GS.GM{dir, GS.unlink(dir, AM(lo, hi, it, at), u, v, su, sv)}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}
  {==}

# ---- two different present vertices ----

def lne(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}) -> {Nat.is_eq(W.lbu(u, KS(lo, hi, it)), W.lbu(v, KS(lo, hi, it))) == False{} : Bool}:
  EO.slots_differ(KS(lo, hi, it), W.lbu(u, KS(lo, hi, it)), W.lbu(v, KS(lo, hi, it)), u, v, fx_eq(dir, lo, hi, depth, it, at, u, h, hu), fx_eq(dir, lo, hi, depth, it, at, v, h, hv), huv, Nat.is_eq(W.lbu(u, KS(lo, hi, it)), W.lbu(v, KS(lo, hi, it))), {==})

def sne(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}) -> {Nat.is_eq(U32.to_nat(IX(lo, hi, it, v)), U32.to_nat(IX(lo, hi, it, u))) == False{} : Bool}:
  +a = L.subst(Nat, z => {Nat.is_eq(z, W.lbu(v, KS(lo, hi, it))) == False{} : Bool}, W.lbu(u, KS(lo, hi, it)), LX(lo, hi, it, u), Equal.sym(Nat, LX(lo, hi, it, u), W.lbu(u, KS(lo, hi, it)), W.lbs_lbu(u, AR.slots(U32, it), Nat.sub(hi, lo), lo)), lne(dir, lo, hi, depth, it, at, u, v, h, hu, hv, huv))
  +b = L.subst(Nat, z => {Nat.is_eq(LX(lo, hi, it, u), z) == False{} : Bool}, W.lbu(v, KS(lo, hi, it)), LX(lo, hi, it, v), Equal.sym(Nat, LX(lo, hi, it, v), W.lbu(v, KS(lo, hi, it)), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo)), a)
  +c = is_eq_add(lo, LX(lo, hi, it, u), LX(lo, hi, it, v), b)
  +d = L.subst(Nat, z => {Nat.is_eq(z, OP.lbv(lo, hi, it, v)) == False{} : Bool}, OP.lbv(lo, hi, it, u), U32.to_nat(IX(lo, hi, it, u)), Equal.sym(Nat, U32.to_nat(IX(lo, hi, it, u)), OP.lbv(lo, hi, it, u), ED.slot_nat(dir, lo, hi, depth, it, at, u, h, fx_hin(dir, lo, hi, depth, it, at, u, hu))), c)
  +e = L.subst(Nat, z => {Nat.is_eq(U32.to_nat(IX(lo, hi, it, u)), z) == False{} : Bool}, OP.lbv(lo, hi, it, v), U32.to_nat(IX(lo, hi, it, v)), Equal.sym(Nat, U32.to_nat(IX(lo, hi, it, v)), OP.lbv(lo, hi, it, v), ED.slot_nat(dir, lo, hi, depth, it, at, v, h, fx_hin(dir, lo, hi, depth, it, at, v, hv))), d)
  SH.ne_flip(U32.to_nat(IX(lo, hi, it, u)), U32.to_nat(IX(lo, hi, it, v)), e)

# ---- the second update (undirected graphs) ----

def B2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<U32>:
  NO.dsel(BX(dir, lo, hi, depth, it, at, v), u, NO.fnd(BX(dir, lo, hi, depth, it, at, v), u))

def AT2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, depth, AT1(dir, lo, hi, depth, it, at, u, v), U32.to_nat(IX(lo, hi, it, v)), B2(dir, lo, hi, depth, it, at, u, v))

def BW1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v))

def hx2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}) -> {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT1(dir, lo, hi, depth, it, at, u, v)), U32.to_nat(IX(lo, hi, it, v))) == Some{BX(dir, lo, hi, depth, it, at, v)} : Maybe<&2, AR.Tree<U32>>}:
  Equal.trans(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT1(dir, lo, hi, depth, it, at, u, v)), U32.to_nat(IX(lo, hi, it, v))), SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(IX(lo, hi, it, v))), Some{BX(dir, lo, hi, depth, it, at, v)},
    EO.tree_other(depth, at, U32.to_nat(IX(lo, hi, it, u)), B1(dir, lo, hi, depth, it, at, u, v), U32.to_nat(IX(lo, hi, it, v)), fx_hi(dir, lo, hi, depth, it, at, u, h, hu), OP.g_adj(dir, lo, hi, depth, it, at, h), sne(dir, lo, hi, depth, it, at, u, v, h, hu, hv, huv)),
    fx_hx(dir, lo, hi, depth, it, at, v, h, hv))

def bw2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}) -> {BW(lo, hi, AT2(dir, lo, hi, depth, it, at, u, v)) == SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v)) : List<&2, AR.Tree<U32>>}:
  Equal.trans(List<&2, AR.Tree<U32>>, BW(lo, hi, AT2(dir, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v)),
    win_after(lo, hi, depth, it, AT1(dir, lo, hi, depth, it, at, u, v), v, B2(dir, lo, hi, depth, it, at, u, v), at1_perfect(dir, lo, hi, depth, it, at, u, v, h), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, v, h, fx_hin(dir, lo, hi, depth, it, at, v, hv)), ED.slot_nat(dir, lo, hi, depth, it, at, v, h, fx_hin(dir, lo, hi, depth, it, at, v, hv))),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v)), BW(lo, hi, AT1(dir, lo, hi, depth, it, at, u, v)), BW1(dir, lo, hi, depth, it, at, u, v), bw1(dir, lo, hi, depth, it, at, u, v, h, hu)))

def am2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {ST.amodel(KS(lo, hi, it), SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v))) == GS.put(v, GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +hlen = Equal.trans(Nat, SC.length(U32, KS(lo, hi, it)), SC.length(AR.Tree<U32>, BW(lo, hi, at)), SC.length(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v)), hlen_of(dir, lo, hi, depth, it, at, h), Equal.sym(Nat, SC.length(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v)), SC.length(AR.Tree<U32>, BW(lo, hi, at)), LL.length_update(AR.Tree<U32>, BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v))))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(KS(lo, hi, it), SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v))), GS.put(v, ST.uset(ST.bents(B2(dir, lo, hi, depth, it, at, u, v))), ST.amodel(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))),
    EO.put_model(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v), v, B2(dir, lo, hi, depth, it, at, u, v), hlen, fx_eq(dir, lo, hi, depth, it, at, v, h, hv)),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.put(v, ST.uset(ST.bents(B2(dir, lo, hi, depth, it, at, u, v))), ST.amodel(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)), ST.amodel(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))),
      Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(v, z, ST.amodel(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v))), ST.uset(ST.bents(B2(dir, lo, hi, depth, it, at, u, v))), GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)),
        NO.dsem(BX(dir, lo, hi, depth, it, at, v), u, fx_bk(dir, lo, hi, depth, it, at, v, h, hv), NO.fnd(BX(dir, lo, hi, depth, it, at, v), u), {==})),
      Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.put(v, GS.sdel(u, SX(dir, lo, hi, depth, it, at, v)), z), ST.amodel(KS(lo, hi, it), BW1(dir, lo, hi, depth, it, at, u, v)), GS.put(u, GS.sdel(v, SX(dir, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)), am1(dir, lo, hi, depth, it, at, u, v, h, hu, efb))))

def blocks2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {ST.blocks_ok(SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v))) == True{} : Bool}:
  EO.blocks_update(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v), blocks1(dir, lo, hi, depth, it, at, u, v, h, hu, efb), NO.dsel_ok(BX(dir, lo, hi, depth, it, at, v), u, fx_bk(dir, lo, hi, depth, it, at, v, h, hv), NO.fnd(BX(dir, lo, hi, depth, it, at, v), u), {==}))

def mdeg2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v))), GT.mdeg(BW(lo, hi, at))) == True{} : Bool}:
  +eb = Equal.trans(AR.Tree<U32>, ED.bnth(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it))), ED.bnth(BW(lo, hi, at), W.lbu(v, KS(lo, hi, it))), BX(dir, lo, hi, depth, it, at, v),
    bnth_upd_other(BW(lo, hi, at), W.lbu(u, KS(lo, hi, it)), B1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), lne(dir, lo, hi, depth, it, at, u, v, h, hu, hv, huv)),
    bnth_lbu(dir, lo, hi, depth, it, at, v))
  +hd = L.subst(AR.Tree<U32>, z => {Nat.is_le(ST.bdeg(B2(dir, lo, hi, depth, it, at, u, v)), ST.bdeg(z)) == True{} : Bool}, BX(dir, lo, hi, depth, it, at, v), ED.bnth(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it))), Equal.sym(AR.Tree<U32>, ED.bnth(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it))), BX(dir, lo, hi, depth, it, at, v), eb),
    dsel_deg(BX(dir, lo, hi, depth, it, at, v), u, fx_bk(dir, lo, hi, depth, it, at, v, h, hv), NO.fnd(BX(dir, lo, hi, depth, it, at, v), u), {==}))
  N.le_trans(GT.mdeg(SC.update(AR.Tree<U32>, BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v))), GT.mdeg(BW1(dir, lo, hi, depth, it, at, u, v)), GT.mdeg(BW(lo, hi, at)),
    GT.mdeg_upd_le(BW1(dir, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(dir, lo, hi, depth, it, at, u, v), hd),
    mdeg1(dir, lo, hi, depth, it, at, u, v, h, hu, efb))

# mu only depends on the window size and the maximum degree.
def mu_le(+d1: Bool, +d2: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +at2: AR.Tree<AR.Tree<U32>>, +hm: {Nat.is_le(GT.mdeg(BW(lo, hi, at2)), GT.mdeg(BW(lo, hi, at))) == True{} : Bool}) -> {Nat.is_le(GT.mu(ST.Sh{d2, lo, hi, depth, it, at2}), Nat.add(GT.mu(ST.Sh{d1, lo, hi, depth, it, at}), 0n)) == True{} : Bool}:
  N.le_trans(GT.mu(ST.Sh{d2, lo, hi, depth, it, at2}), GT.mu(ST.Sh{d1, lo, hi, depth, it, at}), Nat.add(GT.mu(ST.Sh{d1, lo, hi, depth, it, at}), 0n),
    W.add_mono(Nat.sub(hi, lo), GT.mdeg(BW(lo, hi, at2)), GT.mdeg(BW(lo, hi, at)), hm),
    N.le_add_right(GT.mu(ST.Sh{d1, lo, hi, depth, it, at}), 0n))

# ---- remove_edge: the successful branches ----

def gm_done(d: Bool, am: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>) -> GS.Model & E.Obs:
  (GS.GM{d, am}, E.OUnit{Done{Unit{}}})

def g_done(d: Bool, +lo: Nat, +hi: Nat, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{d, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, ids, adj}, Done{Unit{}})

def g_fail(d: Bool, +lo: Nat, +hi: Nat, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{d, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, ids, adj}, Fail{E.EdgeNotFound{}})

def rm_t(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{True{}, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +efb: {NO.fnd(BX(True{}, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> UC.UCore(ST.Sh{True{}, lo, hi, depth, it, at}, G.re_ok(True{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AT1(True{}, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u, True{}), GS.remove_present(True{}, True{}, AM(lo, hi, it, at), u, v, SX(True{}, lo, hi, depth, it, at, u), SX(True{}, lo, hi, depth, it, at, v)), 0n):
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => gm_done(True{}, z), ST.amodel(KS(lo, hi, it), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v))), GS.put(u, GS.sdel(v, SX(True{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v))), ST.amodel(KS(lo, hi, it), BW1(True{}, lo, hi, depth, it, at, u, v)), GS.put(u, GS.sdel(v, SX(True{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(KS(lo, hi, it), z), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)),
      am1(True{}, lo, hi, depth, it, at, u, v, h, hu, efb)))
  +wf = GT.wf_after(True{}, lo, hi, depth, it, at, h, E.RemoveEdge{u, v}, GS.GM{True{}, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{True{}, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}}), (GS.GM{True{}, GS.put(u, GS.sdel(v, SX(True{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{True{}, lo, hi, depth, it, at}), E.RemoveEdge{u, v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{True{}, lo, hi, depth, it, at}), E.RemoveEdge{u, v}), (GS.GM{True{}, GS.unlink(True{}, AM(lo, hi, it, at), u, v, SX(True{}, lo, hi, depth, it, at, u), SX(True{}, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}), spec_rm(True{}, lo, hi, depth, it, at, u, v, h, hu, hv, efb))))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, BW1(True{}, lo, hi, depth, it, at, u, v), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)), blocks1(True{}, lo, hi, depth, it, at, u, v, h, hu, efb))
  +hm = L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(z), GT.mdeg(BW(lo, hi, at))) == True{} : Bool}, BW1(True{}, lo, hi, depth, it, at, u, v), BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, BW(lo, hi, AT1(True{}, lo, hi, depth, it, at, u, v)), BW1(True{}, lo, hi, depth, it, at, u, v), bw1(True{}, lo, hi, depth, it, at, u, v, h, hu)), mdeg1(True{}, lo, hi, depth, it, at, u, v, h, hu, efb))
  UC.uc_mk(ST.Sh{True{}, lo, hi, depth, it, at}, G.re_ok(True{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AT1(True{}, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u, True{}), GS.remove_present(True{}, True{}, AM(lo, hi, it, at), u, v, SX(True{}, lo, hi, depth, it, at, u), SX(True{}, lo, hi, depth, it, at, v)), 0n,
    ST.Sh{True{}, lo, hi, depth, it, AT1(True{}, lo, hi, depth, it, at, u, v)}, Done{Unit{}}, {==},
    GT.good_mk(True{}, lo, hi, depth, it, AT1(True{}, lo, hi, depth, it, at, u, v), OP.g_depth(True{}, lo, hi, depth, it, at, h), OP.g_ids(True{}, lo, hi, depth, it, at, h), at1_perfect(True{}, lo, hi, depth, it, at, u, v, h), OP.g_lohi(True{}, lo, hi, depth, it, at, h), OP.g_cap(True{}, lo, hi, depth, it, at, h), OP.g_asc(True{}, lo, hi, depth, it, at, h), hbl, wf),
    e3, mu_le(True{}, True{}, lo, hi, depth, it, at, AT1(True{}, lo, hi, depth, it, at, u, v), hm))

def rm_f(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{False{}, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +efb: {NO.fnd(BX(False{}, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> UC.UCore(ST.Sh{False{}, lo, hi, depth, it, at}, G.re_ok(False{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AT1(False{}, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u, True{}), GS.remove_present(True{}, False{}, AM(lo, hi, it, at), u, v, SX(False{}, lo, hi, depth, it, at, u), SX(False{}, lo, hi, depth, it, at, v)), 0n):
  +e1 = Equal.cong(G.Upd, G.Graph & Result<&2, &2, E.Error, Unit>, z => g_done(False{}, lo, hi, depth, AR.thaw(U32, it), G.del_nbr_fin(z)), G.del_nbr(A2.thaw2(AT1(False{}, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u), G.UP{A2.thaw2(AT2(False{}, lo, hi, depth, it, at, u, v)), NO.fnd(BX(False{}, lo, hi, depth, it, at, v), u)},
    NO.del_nbr_ok(depth, AT1(False{}, lo, hi, depth, it, at, u, v), IX(lo, hi, it, v), BX(False{}, lo, hi, depth, it, at, v), u, ED.dep32(False{}, lo, hi, depth, it, at, h), fx_hi(False{}, lo, hi, depth, it, at, v, h, hv), hx2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, huv), at1_perfect(False{}, lo, hi, depth, it, at, u, v, h), fx_bk(False{}, lo, hi, depth, it, at, v, h, hv)))
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => gm_done(False{}, z), ST.amodel(KS(lo, hi, it), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sdel(u, SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(False{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v))), ST.amodel(KS(lo, hi, it), SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v))), GS.put(v, GS.sdel(u, SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(False{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at))),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(KS(lo, hi, it), z), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v)), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)),
      am2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, efb)))
  +wf = GT.wf_after(False{}, lo, hi, depth, it, at, h, E.RemoveEdge{u, v}, GS.GM{False{}, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{False{}, ST.amodel(KS(lo, hi, it), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)))}, E.OUnit{Done{Unit{}}}), (GS.GM{False{}, GS.put(v, GS.sdel(u, SX(False{}, lo, hi, depth, it, at, v)), GS.put(u, GS.sdel(v, SX(False{}, lo, hi, depth, it, at, u)), AM(lo, hi, it, at)))}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{False{}, lo, hi, depth, it, at}), E.RemoveEdge{u, v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{False{}, lo, hi, depth, it, at}), E.RemoveEdge{u, v}), (GS.GM{False{}, GS.unlink(False{}, AM(lo, hi, it, at), u, v, SX(False{}, lo, hi, depth, it, at, u), SX(False{}, lo, hi, depth, it, at, v))}, E.OUnit{Done{Unit{}}}), spec_rm(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, efb))))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v)), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v)), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)), blocks2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, efb))
  +hm = L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(z), GT.mdeg(BW(lo, hi, at))) == True{} : Bool}, SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v)), BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), Equal.sym(List<&2, AR.Tree<U32>>, BW(lo, hi, AT2(False{}, lo, hi, depth, it, at, u, v)), SC.update(AR.Tree<U32>, BW1(False{}, lo, hi, depth, it, at, u, v), W.lbu(v, KS(lo, hi, it)), B2(False{}, lo, hi, depth, it, at, u, v)), bw2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv)), mdeg2(False{}, lo, hi, depth, it, at, u, v, h, hu, hv, huv, efb))
  +hpa = AR.upd_perfect(AR.Tree<U32>, depth, AT1(False{}, lo, hi, depth, it, at, u, v), U32.to_nat(IX(lo, hi, it, v)), B2(False{}, lo, hi, depth, it, at, u, v), at1_perfect(False{}, lo, hi, depth, it, at, u, v, h))
  UC.uc_mk(ST.Sh{False{}, lo, hi, depth, it, at}, G.re_ok(False{}, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AT1(False{}, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u, True{}), GS.remove_present(True{}, False{}, AM(lo, hi, it, at), u, v, SX(False{}, lo, hi, depth, it, at, u), SX(False{}, lo, hi, depth, it, at, v)), 0n,
    ST.Sh{False{}, lo, hi, depth, it, AT2(False{}, lo, hi, depth, it, at, u, v)}, Done{Unit{}}, e1,
    GT.good_mk(False{}, lo, hi, depth, it, AT2(False{}, lo, hi, depth, it, at, u, v), OP.g_depth(False{}, lo, hi, depth, it, at, h), OP.g_ids(False{}, lo, hi, depth, it, at, h), hpa, OP.g_lohi(False{}, lo, hi, depth, it, at, h), OP.g_cap(False{}, lo, hi, depth, it, at, h), OP.g_asc(False{}, lo, hi, depth, it, at, h), hbl, wf),
    e3, mu_le(False{}, False{}, lo, hi, depth, it, at, AT2(False{}, lo, hi, depth, it, at, u, v), hm))

def rm_dir(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_ok(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AT1(dir, lo, hi, depth, it, at, u, v)), IX(lo, hi, it, v), u, True{}), GS.remove_present(True{}, dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n):
  match dir:
    case True{}:
      rm_t(lo, hi, depth, it, at, u, v, h, hu, hv, efb)
    case False{}:
      rm_f(lo, hi, depth, it, at, u, v, h, hu, hv, huv, efb)

# ---- remove_edge: the case analysis ----

def re_case4(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, fb: Bool, +efb: {NO.fnd(BX(dir, lo, hi, depth, it, at, u), v) == fb : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_ok(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, fb))), IX(lo, hi, it, v), u, fb), GS.remove_present(fb, dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n):
  match fb:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.re_ok(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, False{}))), IX(lo, hi, it, v), u, False{}), GS.remove_present(False{}, dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n, E.EdgeNotFound{},
        Equal.cong(AR.Tree<AR.Tree<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, t => g_fail(dir, lo, hi, depth, AR.thaw(U32, it), A2.thaw2(t)), AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), BX(dir, lo, hi, depth, it, at, u)), at,
          NO.upd_id(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), BX(dir, lo, hi, depth, it, at, u), fx_hi(dir, lo, hi, depth, it, at, u, h, hu), OP.g_adj(dir, lo, hi, depth, it, at, h), fx_hx(dir, lo, hi, depth, it, at, u, h, hu))),
        {==})
    case True{}:
      rm_dir(dir, lo, hi, depth, it, at, u, v, h, hu, hv, huv, efb)

def re_case3(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, +hv: {FX(lo, hi, it, v) == True{} : Bool}, same: Bool, +es: {U32.is_eq(u, v) == same : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_loop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), IX(lo, hi, it, v), u, v, same), GS.remove_present(GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n):
  match same:
    case True{}:
      +lf = EO.loopfree_find(AM(lo, hi, it, at), u, SX(dir, lo, hi, depth, it, at, u), EO.wf_loopfree(dir, AM(lo, hi, it, at), OP.g_wf(dir, lo, hi, depth, it, at, h)), fx_find(dir, lo, hi, depth, it, at, u, h, hu))
      +hsm = L.subst(U32, z => {GS.smem(z, SX(dir, lo, hi, depth, it, at, u)) == False{} : Bool}, u, v, NO.is_eq_eq(u, v, es), lf)
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.re_loop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), IX(lo, hi, it, v), u, v, True{}), GS.remove_present(GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n, E.EdgeNotFound{}, {==},
        Equal.cong(Bool, GS.Model & E.Obs, b => GS.remove_present(b, dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), False{}, GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), Equal.sym(Bool, GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), False{}, hsm)))
    case False{}:
      L.subst(G.Upd, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_go(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), IX(lo, hi, it, v), u, z), GS.remove_present(GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n),
        G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)))), NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)}, G.del_nbr(A2.thaw2(at), IX(lo, hi, it, u), v),
        Equal.sym(G.Upd, G.del_nbr(A2.thaw2(at), IX(lo, hi, it, u), v), G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)))), NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)},
          NO.del_nbr_ok(depth, at, IX(lo, hi, it, u), BX(dir, lo, hi, depth, it, at, u), v, ED.dep32(dir, lo, hi, depth, it, at, h), fx_hi(dir, lo, hi, depth, it, at, u, h, hu), fx_hx(dir, lo, hi, depth, it, at, u, h, hu), OP.g_adj(dir, lo, hi, depth, it, at, h), fx_bk(dir, lo, hi, depth, it, at, u, h, hu))),
        L.subst(Bool, b => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_ok(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(IX(lo, hi, it, u)), NO.dsel(BX(dir, lo, hi, depth, it, at, u), v, NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)))), IX(lo, hi, it, v), u, NO.fnd(BX(dir, lo, hi, depth, it, at, u), v)), GS.remove_present(b, dir, AM(lo, hi, it, at), u, v, SX(dir, lo, hi, depth, it, at, u), SX(dir, lo, hi, depth, it, at, v)), 0n),
          NO.fnd(BX(dir, lo, hi, depth, it, at, u), v), GS.smem(v, SX(dir, lo, hi, depth, it, at, u)), NO.e_is_some(BX(dir, lo, hi, depth, it, at, u), v, fx_bk(dir, lo, hi, depth, it, at, u, h, hu)),
          re_case4(dir, lo, hi, depth, it, at, u, v, h, hu, hv, es, NO.fnd(BX(dir, lo, hi, depth, it, at, u), v), {==})))

def re_case2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {FX(lo, hi, it, u) == True{} : Bool}, fv: Bool, +efv: {FX(lo, hi, it, v) == fv : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), IX(lo, hi, it, v), u, v, fv), GS.remove_edge_at(Some{SX(dir, lo, hi, depth, it, at, u)}, LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, SX(dir, lo, hi, depth, it, at, v)), dir, AM(lo, hi, it, at), u, v), 0n):
  match fv:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.re_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), IX(lo, hi, it, v), u, v, False{}), GS.remove_edge_at(Some{SX(dir, lo, hi, depth, it, at, u)}, LB.pickv(List<&2, BE.Entry<U32, Unit>>, False{}, SX(dir, lo, hi, depth, it, at, v)), dir, AM(lo, hi, it, at), u, v), 0n, E.VertexNotFound{}, {==}, {==})
    case True{}:
      re_case3(dir, lo, hi, depth, it, at, u, v, h, hu, efv, U32.is_eq(u, v), {==})

def re_case1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, fu: Bool, +efu: {FX(lo, hi, it, u) == fu : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), u, v, fu), GS.remove_edge_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, fu, SX(dir, lo, hi, depth, it, at, u)), GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v), 0n):
  match fu:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.re_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), u, v, False{}), GS.remove_edge_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, False{}, SX(dir, lo, hi, depth, it, at, u)), GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v), 0n, E.VertexNotFound{}, {==}, {==})
    case True{}:
      L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_v(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), IX(lo, hi, it, u), u, v, z), GS.remove_edge_at(Some{SX(dir, lo, hi, depth, it, at, u)}, GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v), 0n),
        G.LC{AR.thaw(U32, it), IX(lo, hi, it, v), FX(lo, hi, it, v)}, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
        Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), IX(lo, hi, it, v), FX(lo, hi, it, v)}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)),
        L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), IX(lo, hi, it, v), u, v, FX(lo, hi, it, v)), GS.remove_edge_at(Some{SX(dir, lo, hi, depth, it, at, u)}, m, dir, AM(lo, hi, it, at), u, v), 0n),
          LB.pickv(List<&2, BE.Entry<U32, Unit>>, FX(lo, hi, it, v), SX(dir, lo, hi, depth, it, at, v)), GS.find(v, AM(lo, hi, it, at)),
          Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, FX(lo, hi, it, v), SX(dir, lo, hi, depth, it, at, v)), ED.gfind(dir, lo, hi, depth, it, at, v, h)),
          re_case2(dir, lo, hi, depth, it, at, u, v, h, efu, FX(lo, hi, it, v), {==})))

def rm_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.remove_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveEdge{u, v}), 0n):
  L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_u(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), u, v, z), GS.remove_edge_at(GS.find(u, AM(lo, hi, it, at)), GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v), 0n),
    G.LC{AR.thaw(U32, it), IX(lo, hi, it, u), FX(lo, hi, it, u)}, G.locate(depth, u, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
    Equal.sym(G.Loc, G.locate(depth, u, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), IX(lo, hi, it, u), FX(lo, hi, it, u)}, OP.hv_locate(dir, lo, hi, depth, it, at, u, h)),
    L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.re_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), IX(lo, hi, it, u), u, v, FX(lo, hi, it, u)), GS.remove_edge_at(m, GS.find(v, AM(lo, hi, it, at)), dir, AM(lo, hi, it, at), u, v), 0n),
      LB.pickv(List<&2, BE.Entry<U32, Unit>>, FX(lo, hi, it, u), SX(dir, lo, hi, depth, it, at, u)), GS.find(u, AM(lo, hi, it, at)),
      Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, FX(lo, hi, it, u), SX(dir, lo, hi, depth, it, at, u)), ED.gfind(dir, lo, hi, depth, it, at, u, h)),
      re_case1(dir, lo, hi, depth, it, at, u, v, h, FX(lo, hi, it, u), {==})))

# remove_edge refines the specification, preserves the invariant and does not grow the measure.
def so_remove_edge(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> GT.StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.RemoveEdge{u, v}):
  UC.uc_step(ST.Sh{dir, lo, hi, depth, it, at}, E.RemoveEdge{u, v}, G.remove_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v), rm_core(dir, lo, hi, depth, it, at, u, v, h), {==})
