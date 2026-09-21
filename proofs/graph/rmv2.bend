import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../binary_heap/u32idx.bend as IX
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./window.bend as W
import ./search.bend as SE
import ./ops.bend as OP
import ./blk.bend as BK
import ./edge.bend as ED
import ./shift.bend as SH
import ./blkops.bend as BO
import ./gstep.bend as GT
import ./zip.bend as ZP
import ./ashift.bend as AS2
import ./rmedge.bend as RM
import ./ucore.bend as UC
import ./addv1.bend as AV
import ./addv1.bend as AV
import ./addv2.bend as AV2
import ./rmv1.bend as RV

# remove_vertex, part 2: closing the gap at v's slot by shifting the head
# right (the window starts one later) or the tail left (it ends one earlier),
# for any adjacency tree whose window is the stripped block list with some
# block x left at v's slot.

def WS(+v: U32, +lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: AR.Tree<U32>) -> List<&2, AR.Tree<U32>>:
  SC.append(AR.Tree<U32>, RV.dsl(v, AV.ABW(lo, hi, it, at, v)), Con{x, RV.dsl(v, RV.BBd(lo, hi, it, at, v))})

def ws_take(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +x: AR.Tree<U32>) -> {SC.take(AR.Tree<U32>, WS(v, lo, hi, it, at, x), AV.LV(lo, hi, it, v)) == RV.dsl(v, AV.ABW(lo, hi, it, at, v)) : List<&2, AR.Tree<U32>>}:
  +p = RV.dsl(v, AV.ABW(lo, hi, it, at, v))
  +lp = Equal.trans(Nat, SC.length(AR.Tree<U32>, p), SC.length(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v)), AV.LV(lo, hi, it, v), RV.len_dsl(v, AV.ABW(lo, hi, it, at, v)), AV.av_lenba(dir, lo, hi, depth, it, at, v, h))
  L.subst(Nat, n => {SC.take(AR.Tree<U32>, WS(v, lo, hi, it, at, x), n) == p : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, p), AV.LV(lo, hi, it, v), lp, ZP.take_app_exact(AR.Tree<U32>, p, Con{x, RV.dsl(v, RV.BBd(lo, hi, it, at, v))}))

def ws_drop(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +x: AR.Tree<U32>) -> {SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+AV.LV(lo, hi, it, v)) == RV.dsl(v, RV.BBd(lo, hi, it, at, v)) : List<&2, AR.Tree<U32>>}:
  +p = RV.dsl(v, AV.ABW(lo, hi, it, at, v))
  +lp = Equal.trans(Nat, SC.length(AR.Tree<U32>, p), SC.length(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v)), AV.LV(lo, hi, it, v), RV.len_dsl(v, AV.ABW(lo, hi, it, at, v)), AV.av_lenba(dir, lo, hi, depth, it, at, v, h))
  L.subst(Nat, n => {SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+n) == RV.dsl(v, RV.BBd(lo, hi, it, at, v)) : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, p), AV.LV(lo, hi, it, v), lp, ZP.drop_app_len1(AR.Tree<U32>, p, x, RV.dsl(v, RV.BBd(lo, hi, it, at, v))))

def ws_split(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +x: AR.Tree<U32>, +k1: Nat, +w: List<&2, AR.Tree<U32>>, +hw: {w == WS(v, lo, hi, it, at, x) : List<&2, AR.Tree<U32>>}) -> {SC.append(AR.Tree<U32>, SC.take(AR.Tree<U32>, w, AV.LV(lo, hi, it, v)), SC.drop(AR.Tree<U32>, w, 1n+AV.LV(lo, hi, it, v))) == RV.DB(lo, hi, it, at, v) : List<&2, AR.Tree<U32>>}:
  L.subst(List<&2, AR.Tree<U32>>, z => {SC.append(AR.Tree<U32>, SC.take(AR.Tree<U32>, z, AV.LV(lo, hi, it, v)), SC.drop(AR.Tree<U32>, z, 1n+AV.LV(lo, hi, it, v))) == RV.DB(lo, hi, it, at, v) : List<&2, AR.Tree<U32>>}, WS(v, lo, hi, it, at, x), w, Equal.sym(List<&2, AR.Tree<U32>>, w, WS(v, lo, hi, it, at, x), hw),
    Equal.trans(List<&2, AR.Tree<U32>>, SC.append(AR.Tree<U32>, SC.take(AR.Tree<U32>, WS(v, lo, hi, it, at, x), AV.LV(lo, hi, it, v)), SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+AV.LV(lo, hi, it, v))), SC.append(AR.Tree<U32>, RV.dsl(v, AV.ABW(lo, hi, it, at, v)), SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+AV.LV(lo, hi, it, v))), RV.DB(lo, hi, it, at, v),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.append(AR.Tree<U32>, z, SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+AV.LV(lo, hi, it, v))), SC.take(AR.Tree<U32>, WS(v, lo, hi, it, at, x), AV.LV(lo, hi, it, v)), RV.dsl(v, AV.ABW(lo, hi, it, at, v)), ws_take(dir, lo, hi, depth, it, at, v, h, x)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.append(AR.Tree<U32>, RV.dsl(v, AV.ABW(lo, hi, it, at, v)), z), SC.drop(AR.Tree<U32>, WS(v, lo, hi, it, at, x), 1n+AV.LV(lo, hi, it, v)), RV.dsl(v, RV.BBd(lo, hi, it, at, v)), ws_drop(dir, lo, hi, depth, it, at, v, h, x))))

def sub_pred2(+hi: Nat, +lo: Nat, +h: {Nat.is_le(1n+lo, hi) == True{} : Bool}) -> {Nat.sub(hi, lo) == 1n+Nat.sub(Nat.sub(hi, 1n), lo) : Nat}:
  match hi:
    case 0n:
      Empty.absurd({Nat.sub(0n, lo) == 1n+Nat.sub(Nat.sub(0n, 1n), lo) : Nat}, L.false_true(h))
    case 1n+q:
      Equal.trans(Nat, Nat.sub(1n+q, lo), 1n+Nat.sub(q, lo), 1n+Nat.sub(Nat.sub(1n+q, 1n), lo), BO.sub_succ_l(q, lo, h),
        Equal.cong(Nat, Nat, z => 1n+Nat.sub(z, lo), q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(1n+q, 1n), q, N.sub_zero(q))))

def RVH(+dir: Bool, +lo: Nat, +hi: Nat, +d: Nat, +k: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{dir, U32.from_nat(1n+lo), U32.from_nat(hi), U.pow2u(d), d, G.shr_go(k, i, ids), G.shra_go(k, i, adj)}, Done{Unit{}})

def RVT(+dir: Bool, +lo: Nat, +hj: U32, +d: Nat, +k: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{dir, U32.from_nat(lo), hj, U.pow2u(d), d, G.shl_go(k, i, ids), G.shla_go(k, i, adj)}, Done{Unit{}})

def RVTK(+dir: Bool, +lo: Nat, +hj: U32, +d: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  RVT(dir, lo, hj, d, U32.to_nat(U32.sub(hj, i)), i, ids, adj)

def RVR(g: G.Graph) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (g, Done{Unit{}})

def sub1_lt(+hi: Nat, +h: {Nat.is_le(1n, hi) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(hi, 1n), hi) == True{} : Bool}:
  match hi:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, L.false_true(h))
    case 1n+q:
      L.subst(Nat, z => {Nat.is_lt(z, 1n+q) == True{} : Bool}, q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(1n+q, 1n), q, N.sub_zero(q)), N.lt_succ(q))

def rv_head_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}, +at1: AR.Tree<AR.Tree<U32>>, +x: AR.Tree<U32>, +hpa1: {AR.perfect(AR.Tree<U32>, depth, at1) == True{} : Bool}, +hw1: {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at1), lo, Nat.sub(hi, lo)) == WS(v, lo, hi, it, at, x) : List<&2, AR.Tree<U32>>}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, RVR(G.rv_head(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), AR.thaw(U32, it), A2.thaw2(at1))), (GS.GM{dir, RV.DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n):
  +l = AV.LV(lo, hi, it, v)
  +k1 = Nat.sub(hi, 1n+lo)
  +i = Nat.add(lo, l)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hk32 = OP.g_depth(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, lo, hi, depth, it, at, h)
  +hin = RM.fx_hin(dir, lo, hi, depth, it, at, v, hf)
  +hlo1 = N.le_trans(1n+lo, 1n+i, hi, N.le_add_right(1n+lo, l), N.lt_succ_le_succ(i, hi, hin))
  +hk = AV2.sub_pred(hi, lo, hlo1)
  +hl = N.lt_succ_le(l, k1, L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, RV.rv_lt(dir, lo, hi, depth, it, at, v, h, hf)))
  +hir = N.lt_le_trans(i, hi, SC.pow2(depth), hin, hcap)
  +hli = L.subst(Nat, z => {Nat.is_le(l, z) == True{} : Bool}, Nat.add(l, lo), i, N.add_comm(l, lo), N.le_add_right(l, lo))
  +u = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(i), U32.from_nat(lo))), U32.to_nat(U32.from_nat(Nat.sub(i, lo))), l,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(i), U32.from_nat(lo)), U32.from_nat(Nat.sub(i, lo)), H.sub_bridge(i, lo, 1n+depth, hk32, AV2.lt_up(i, depth, N.lt_le(i, SC.pow2(depth), hir)), N.le_add_right(lo, l))),
    Equal.trans(Nat, U32.to_nat(U32.from_nat(Nat.sub(i, lo))), U32.to_nat(U32.from_nat(l)), l,
      Equal.cong(Nat, Nat, z => U32.to_nat(U32.from_nat(z)), Nat.sub(i, lo), l, N.add_sub_cancel(lo, l)),
      IX.nat_round(l, 1n+depth, hk32, AV2.lt_up(l, depth, N.le_trans(l, i, SC.pow2(depth), hli, N.lt_le(i, SC.pow2(depth), hir))))))
  +st1 = SH.shr_tree(l, depth, it, i)
  +sa1 = AS2.shra_tree(l, depth, at1, i)
  +e1 = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, RVH(dir, lo, hi, depth, U32.to_nat(U32.sub(U32.from_nat(i), U32.from_nat(lo))), U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RVH(dir, lo, hi, depth, l, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RM.g_done(dir, 1n+lo, hi, depth, AR.thaw(U32, st1), A2.thaw2(sa1)),
    Equal.cong(Nat, G.Graph & Result<&2, &2, E.Error, Unit>, n => RVH(dir, lo, hi, depth, n, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), U32.to_nat(U32.sub(U32.from_nat(i), U32.from_nat(lo))), l, u),
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, RVH(dir, lo, hi, depth, l, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RM.g_done(dir, 1n+lo, hi, depth, AR.thaw(U32, st1), G.shra_go(l, U32.from_nat(i), A2.thaw2(at1))), RM.g_done(dir, 1n+lo, hi, depth, AR.thaw(U32, st1), A2.thaw2(sa1)),
      Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, 1n+lo, hi, depth, z, G.shra_go(l, U32.from_nat(i), A2.thaw2(at1))), G.shr_go(l, U32.from_nat(i), AR.thaw(U32, it)), AR.thaw(U32, st1), SH.shr_run(l, depth, it, i, hd, pfi, hir, hli)),
      Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, 1n+lo, hi, depth, AR.thaw(U32, st1), z), G.shra_go(l, U32.from_nat(i), A2.thaw2(at1)), A2.thaw2(sa1), AS2.sra_run(l, depth, at1, i, hd, hpa1, hir, hli))))
  +hk1 = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, z), SC.length(U32, AR.slots(U32, it))) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, ED.win_fits(U32, depth, it, lo, hi, pfi, hlo, hcap))
  +hkb = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, z), SC.length(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at1))) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, ED.win_fits(AR.Tree<U32>, depth, at1, lo, hi, hpa1, hlo, hcap))
  +xs = AR.slots(U32, it)
  +hwk = Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, AR.slots(U32, st1), 1n+lo), k1), SC.take(U32, SC.drop(U32, ZP.lsr(U32, False{}, 0, 0, l, xs, i), 1n+lo), k1), RV.DK(lo, hi, it, v),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.take(U32, SC.drop(U32, z, 1n+lo), k1), AR.slots(U32, st1), ZP.lsr(U32, False{}, 0, 0, l, xs, i), AS2.sr_slots(l, depth, it, i, pfi, hir, hli)),
    Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, ZP.lsr(U32, False{}, 0, 0, l, xs, i), 1n+lo), k1), SC.append(U32, SC.take(U32, SC.take(U32, SC.drop(U32, xs, lo), 1n+k1), l), SC.drop(U32, SC.take(U32, SC.drop(U32, xs, lo), 1n+k1), 1n+l)), RV.DK(lo, hi, it, v),
      ZP.del_right_win(U32, False{}, 0, 0, xs, lo, k1, l, hl, hk1),
      Equal.cong(Nat, List<&2, U32>, n => SC.append(U32, SC.take(U32, SC.take(U32, SC.drop(U32, xs, lo), n), l), SC.drop(U32, SC.take(U32, SC.drop(U32, xs, lo), n), 1n+l)), 1n+k1, Nat.sub(hi, lo), Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk))))
  +bs = AR.slots(AR.Tree<U32>, at1)
  +w1 = SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, bs, lo), 1n+k1)
  +hww = Equal.trans(List<&2, AR.Tree<U32>>, w1, ST.win(AR.Tree<U32>, bs, lo, Nat.sub(hi, lo)), WS(v, lo, hi, it, at, x), Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, bs, lo), n), 1n+k1, Nat.sub(hi, lo), Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk)), hw1)
  +hwb = Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, sa1), 1n+lo), k1), SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, bs, i), 1n+lo), k1), RV.DB(lo, hi, it, at, v),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, z, 1n+lo), k1), AR.slots(AR.Tree<U32>, sa1), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, bs, i), AS2.sra_slots(l, depth, at1, i, hpa1, hir, hli)),
    Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, bs, i), 1n+lo), k1), SC.append(AR.Tree<U32>, SC.take(AR.Tree<U32>, w1, l), SC.drop(AR.Tree<U32>, w1, 1n+l)), RV.DB(lo, hi, it, at, v),
      ZP.del_right_win(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), bs, lo, k1, l, hl, hkb),
      ws_split(dir, lo, hi, depth, it, at, v, h, x, k1, w1, hww)))
  RV.rv_new(dir, lo, hi, depth, it, at, v, h, hf, 1n+lo, hi, depth, st1, sa1, RVR(G.rv_head(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), AR.thaw(U32, it), A2.thaw2(at1))), e1,
    Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk), hwk, hwb, hk32, BO.shr_perfect(l, depth, it, i, pfi), AS2.shra_perfect(l, depth, at1, i, hpa1), hlo1, hcap)

def rv_tail_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}, +at1: AR.Tree<AR.Tree<U32>>, +x: AR.Tree<U32>, +hpa1: {AR.perfect(AR.Tree<U32>, depth, at1) == True{} : Bool}, +hw1: {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at1), lo, Nat.sub(hi, lo)) == WS(v, lo, hi, it, at, x) : List<&2, AR.Tree<U32>>}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, RVR(G.rv_tail(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), AR.thaw(U32, it), A2.thaw2(at1))), (GS.GM{dir, RV.DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n):
  +l = AV.LV(lo, hi, it, v)
  +h1 = Nat.sub(hi, 1n)
  +k1 = Nat.sub(h1, lo)
  +i = Nat.add(lo, l)
  +m = Nat.sub(k1, l)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hk32 = OP.g_depth(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, lo, hi, depth, it, at, h)
  +hin = RM.fx_hin(dir, lo, hi, depth, it, at, v, hf)
  +hlo1 = N.le_trans(1n+lo, 1n+i, hi, N.le_add_right(1n+lo, l), N.lt_succ_le_succ(i, hi, hin))
  +h1hi = N.le_trans(1n, 1n+lo, hi, N.lt_succ_le_succ(0n, 1n+lo, {==}), hlo1)
  +hk = sub_pred2(hi, lo, hlo1)
  +hl = N.lt_succ_le(l, k1, L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, RV.rv_lt(dir, lo, hi, depth, it, at, v, h, hf)))
  +hih1 = SH.le_pred(i, hi, N.lt_succ_le_succ(i, hi, hin))
  +hloh1 = N.le_trans(lo, i, h1, N.le_add_right(lo, l), hih1)
  +h1lt = N.lt_le_trans(h1, hi, SC.pow2(depth), sub1_lt(hi, h1hi), hcap)
  +h1le = N.lt_le(h1, SC.pow2(depth), h1lt)
  +u1 = IX.sub_one(hi, 1n+depth, hk32, AV2.lt_up(hi, depth, hcap), h1hi)
  +em = Equal.sym(Nat, Nat.sub(k1, l), Nat.sub(h1, i), SE.sub_add_eq(h1, lo, l))
  +u = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(h1), U32.from_nat(i))), U32.to_nat(U32.from_nat(Nat.sub(h1, i))), m,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(h1), U32.from_nat(i)), U32.from_nat(Nat.sub(h1, i)), H.sub_bridge(h1, i, 1n+depth, hk32, AV2.lt_up(h1, depth, h1le), hih1)),
    Equal.trans(Nat, U32.to_nat(U32.from_nat(Nat.sub(h1, i))), U32.to_nat(U32.from_nat(m)), m,
      Equal.cong(Nat, Nat, z => U32.to_nat(U32.from_nat(z)), Nat.sub(h1, i), m, em),
      IX.nat_round(m, 1n+depth, hk32, AV2.lt_up(m, depth, N.le_trans(m, h1, SC.pow2(depth), N.le_trans(m, k1, h1, H.sub_le(k1, l), H.sub_le(h1, lo)), h1le)))))
  +eix = Equal.trans(Nat, Nat.add(i, m), Nat.add(lo, k1), h1,
    Equal.trans(Nat, Nat.add(i, m), Nat.add(lo, Nat.add(l, m)), Nat.add(lo, k1), N.add_assoc(lo, l, m), Equal.cong(Nat, Nat, z => Nat.add(lo, z), Nat.add(l, m), k1, N.sub_add(k1, l, hl))),
    W.window_end(lo, h1, k1, {==}, hloh1))
  +hjk = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, h1, Nat.add(i, m), Equal.sym(Nat, Nat.add(i, m), h1, eix), h1lt)
  +st1 = SH.shl_tree(m, depth, it, i)
  +sa1 = AS2.shla_tree(m, depth, at1, i)
  +e1 = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, RVTK(dir, lo, U32.sub(U32.from_nat(hi), 1), depth, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RVTK(dir, lo, U32.from_nat(h1), depth, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RM.g_done(dir, lo, h1, depth, AR.thaw(U32, st1), A2.thaw2(sa1)),
    Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => RVTK(dir, lo, z, depth, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), U32.sub(U32.from_nat(hi), 1), U32.from_nat(h1), u1),
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, RVT(dir, lo, U32.from_nat(h1), depth, U32.to_nat(U32.sub(U32.from_nat(h1), U32.from_nat(i))), U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RVT(dir, lo, U32.from_nat(h1), depth, m, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RM.g_done(dir, lo, h1, depth, AR.thaw(U32, st1), A2.thaw2(sa1)),
      Equal.cong(Nat, G.Graph & Result<&2, &2, E.Error, Unit>, n => RVT(dir, lo, U32.from_nat(h1), depth, n, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), U32.to_nat(U32.sub(U32.from_nat(h1), U32.from_nat(i))), m, u),
      Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, RVT(dir, lo, U32.from_nat(h1), depth, m, U32.from_nat(i), AR.thaw(U32, it), A2.thaw2(at1)), RM.g_done(dir, lo, h1, depth, AR.thaw(U32, st1), G.shla_go(m, U32.from_nat(i), A2.thaw2(at1))), RM.g_done(dir, lo, h1, depth, AR.thaw(U32, st1), A2.thaw2(sa1)),
        Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo, h1, depth, z, G.shla_go(m, U32.from_nat(i), A2.thaw2(at1))), G.shl_go(m, U32.from_nat(i), AR.thaw(U32, it)), AR.thaw(U32, st1), SH.shl_run(m, depth, it, i, hd, pfi, hjk)),
        Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo, h1, depth, AR.thaw(U32, st1), z), G.shla_go(m, U32.from_nat(i), A2.thaw2(at1)), A2.thaw2(sa1), AS2.sla_run(m, depth, at1, i, hd, hpa1, hjk)))))
  +hk1 = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, z), SC.length(U32, AR.slots(U32, it))) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, ED.win_fits(U32, depth, it, lo, hi, pfi, hlo, hcap))
  +hkb = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, z), SC.length(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at1))) == True{} : Bool}, Nat.sub(hi, lo), 1n+k1, hk, ED.win_fits(AR.Tree<U32>, depth, at1, lo, hi, hpa1, hlo, hcap))
  +xs = AR.slots(U32, it)
  +hwk = Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, AR.slots(U32, st1), lo), k1), SC.take(U32, SC.drop(U32, ZP.lsl(U32, False{}, 0, 0, m, xs, i), lo), k1), RV.DK(lo, hi, it, v),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.take(U32, SC.drop(U32, z, lo), k1), AR.slots(U32, st1), ZP.lsl(U32, False{}, 0, 0, m, xs, i), AS2.sl_slots(m, depth, it, i, pfi, hjk)),
    Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, ZP.lsl(U32, False{}, 0, 0, m, xs, i), lo), k1), SC.append(U32, SC.take(U32, SC.take(U32, SC.drop(U32, xs, lo), 1n+k1), l), SC.drop(U32, SC.take(U32, SC.drop(U32, xs, lo), 1n+k1), 1n+l)), RV.DK(lo, hi, it, v),
      ZP.del_left_win(U32, False{}, 0, 0, xs, lo, k1, l, hl, hk1),
      Equal.cong(Nat, List<&2, U32>, n => SC.append(U32, SC.take(U32, SC.take(U32, SC.drop(U32, xs, lo), n), l), SC.drop(U32, SC.take(U32, SC.drop(U32, xs, lo), n), 1n+l)), 1n+k1, Nat.sub(hi, lo), Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk))))
  +bs = AR.slots(AR.Tree<U32>, at1)
  +w1 = SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, bs, lo), 1n+k1)
  +hww = Equal.trans(List<&2, AR.Tree<U32>>, w1, ST.win(AR.Tree<U32>, bs, lo, Nat.sub(hi, lo)), WS(v, lo, hi, it, at, x), Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, bs, lo), n), 1n+k1, Nat.sub(hi, lo), Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk)), hw1)
  +hwb = Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, sa1), lo), k1), SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, bs, i), lo), k1), RV.DB(lo, hi, it, at, v),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, z, lo), k1), AR.slots(AR.Tree<U32>, sa1), ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, bs, i), AS2.sla_slots(m, depth, at1, i, hpa1, hjk)),
    Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, bs, i), lo), k1), SC.append(AR.Tree<U32>, SC.take(AR.Tree<U32>, w1, l), SC.drop(AR.Tree<U32>, w1, 1n+l)), RV.DB(lo, hi, it, at, v),
      ZP.del_left_win(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), bs, lo, k1, l, hl, hkb),
      ws_split(dir, lo, hi, depth, it, at, v, h, x, k1, w1, hww)))
  RV.rv_new(dir, lo, hi, depth, it, at, v, h, hf, lo, h1, depth, st1, sa1, RVR(G.rv_tail(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), AR.thaw(U32, it), A2.thaw2(at1))), e1,
    Equal.sym(Nat, Nat.sub(hi, lo), 1n+k1, hk), hwk, hwb, hk32, BO.shl_perfect(m, depth, it, i, pfi), AS2.shla_perfect(m, depth, at1, i, hpa1), hloh1, N.le_trans(h1, hi, SC.pow2(depth), IX.sub_le(hi), hcap))
