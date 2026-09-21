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

# add_vertex, part 2: the two in-place insertions (shift the head left into
# a free slot before the window, or the tail right into a free slot after it).

def sub_pred(+hi: Nat, +lo1: Nat, +h: {Nat.is_le(1n+lo1, hi) == True{} : Bool}) -> {Nat.sub(hi, lo1) == 1n+Nat.sub(hi, 1n+lo1) : Nat}:
  match hi:
    case 0n:
      Empty.absurd({Nat.sub(0n, lo1) == 1n+Nat.sub(0n, 1n+lo1) : Nat}, L.false_true(h))
    case 1n+q:
      BO.sub_succ_l(q, lo1, h)

def lt_up(+x: Nat, +d: Nat, +h: {Nat.is_le(x, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(x, SC.pow2(1n+d)) == True{} : Bool}:
  N.le_lt_trans(x, SC.pow2(d), SC.pow2(1n+d), h, N.pow2_lt_succ(d))

# The result shape of av_left before the index arithmetic is resolved.
def AVL(+dir: Bool, +j: U32, +k: Nat, +w: U32, +hi: Nat, +d: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +v: U32) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{dir, j, U32.from_nat(hi), U.pow2u(d), d, Array.set(U32, G.shl_go(k, j, ids), w, v), Array.set(Array<U32>, G.shla_go(k, j, adj), w, G.empty_blk())}, Done{Unit{}})

def AVR(+dir: Bool, +lo: Nat, +hi: Nat, +k: Nat, +w: U32, +d: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +v: U32) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  (G.G{dir, U32.from_nat(lo), U32.from_nat(1n+hi), U.pow2u(d), d, Array.set(U32, G.shr_go(k, U32.from_nat(hi), ids), w, v), Array.set(Array<U32>, G.shra_go(k, U32.from_nat(hi), adj), w, G.empty_blk())}, Done{Unit{}})

def IT2L(+lo1: Nat, +hi: Nat, +d: Nat, +it: AR.Tree<U32>, +v: U32) -> AR.Tree<U32>:
  AR.upd(U32, d, SH.shl_tree(AV.LV(1n+lo1, hi, it, v), d, it, lo1), Nat.add(lo1, AV.LV(1n+lo1, hi, it, v)), v)

def AT2L(+lo1: Nat, +hi: Nat, +d: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, d, AS2.shla_tree(AV.LV(1n+lo1, hi, it, v), d, at, lo1), Nat.add(lo1, AV.LV(1n+lo1, hi, it, v)), AV.ebt())

# ---- shifting the head left ----

def av_left_core(+dir: Bool, +lo1: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, 1n+lo1, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(1n+lo1, hi, it, v) == False{} : Bool}) -> UC.UCore(ST.Sh{dir, 1n+lo1, hi, depth, it, at}, G.av_left(dir, U32.from_nat(1n+lo1), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(1n+lo1, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(1n+lo1, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  +l = AV.LV(1n+lo1, hi, it, v)
  +k = Nat.sub(hi, 1n+lo1)
  +j = Nat.add(lo1, l)
  +hd = ED.dep32(dir, 1n+lo1, hi, depth, it, at, h)
  +hk32 = OP.g_depth(dir, 1n+lo1, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, 1n+lo1, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, 1n+lo1, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, 1n+lo1, hi, depth, it, at, h)
  +pfa = OP.g_adj(dir, 1n+lo1, hi, depth, it, at, h)
  +hl = AV.av_hl(1n+lo1, hi, it, v)
  +hjl = L.subst(Nat, z => {Nat.is_le(Nat.add(1n+lo1, l), z) == True{} : Bool}, Nat.add(1n+lo1, k), hi, W.window_end(1n+lo1, hi, k, {==}, hlo), W.add_mono(1n+lo1, l, k, hl))
  +hjc = N.le_trans(1n+j, hi, SC.pow2(depth), hjl, hcap)
  +hj = N.lt_le_trans(j, 1n+j, SC.pow2(depth), N.lt_succ(j), hjc)
  +rj = IX.nat_round(j, depth, N.lt_le(depth, 32n, hd), hj)
  +u1 = Equal.trans(U32, U32.sub(U32.from_nat(1n+lo1), 1), U32.from_nat(Nat.sub(1n+lo1, 1n)), U32.from_nat(lo1),
    IX.sub_one(1n+lo1, 1n+depth, hk32, lt_up(1n+lo1, depth, N.le_trans(1n+lo1, hi, SC.pow2(depth), hlo, hcap)), N.lt_succ_le_succ(0n, 1n+lo1, {==})),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+lo1, 1n), lo1, N.sub_zero(lo1)))
  +hl2 = N.le_trans(l, k, SC.pow2(depth), hl, N.le_trans(k, hi, SC.pow2(depth), H.sub_le(hi, 1n+lo1), hcap))
  +u2 = Equal.trans(Nat, U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), U32.to_nat(U32.from_nat(Nat.sub(Nat.add(1n+lo1, l), 1n+lo1))), l,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1)), U32.from_nat(Nat.sub(Nat.add(1n+lo1, l), 1n+lo1)),
      H.sub_bridge(Nat.add(1n+lo1, l), 1n+lo1, 1n+depth, hk32, lt_up(1n+j, depth, hjc), N.le_add_right(1n+lo1, l))),
    Equal.trans(Nat, U32.to_nat(U32.from_nat(Nat.sub(Nat.add(1n+lo1, l), 1n+lo1))), U32.to_nat(U32.from_nat(l)), l,
      Equal.cong(Nat, Nat, z => U32.to_nat(U32.from_nat(z)), Nat.sub(Nat.add(1n+lo1, l), 1n+lo1), l, N.add_sub_cancel(1n+lo1, l)),
      IX.nat_round(l, 1n+depth, hk32, lt_up(l, depth, hl2))))
  +u3 = Equal.trans(U32, U32.sub(RM.IX(1n+lo1, hi, it, v), 1), U32.from_nat(Nat.sub(1n+j, 1n)), U32.from_nat(j),
    IX.sub_one(1n+j, 1n+depth, hk32, lt_up(1n+j, depth, hjc), N.lt_succ_le_succ(0n, 1n+j, {==})),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+j, 1n), j, N.sub_zero(j)))
  +st1 = SH.shl_tree(l, depth, it, lo1)
  +sa1 = AS2.shla_tree(l, depth, at, lo1)
  +pst = BO.shl_perfect(l, depth, it, lo1, pfi)
  +psa = AS2.shla_perfect(l, depth, at, lo1, pfa)
  +ea = Equal.trans(Array<U32>, Array.set(U32, G.shl_go(l, U32.from_nat(lo1), AR.thaw(U32, it)), U32.from_nat(j), v), Array.set(U32, AR.thaw(U32, st1), U32.from_nat(j), v), AR.thaw(U32, IT2L(lo1, hi, depth, it, v)),
    Equal.cong(Array<U32>, Array<U32>, z => Array.set(U32, z, U32.from_nat(j), v), G.shl_go(l, U32.from_nat(lo1), AR.thaw(U32, it)), AR.thaw(U32, st1), SH.shl_run(l, depth, it, lo1, hd, pfi, hj)),
    SH.set_at(depth, st1, j, v, hd, pst, hj, rj))
  +eb = Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), U32.from_nat(j), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(j), AR.thaw(U32, AV.ebt())), A2.thaw2(AT2L(lo1, hi, depth, it, at, v)),
    Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), U32.from_nat(j), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(j), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(j), AR.thaw(U32, AV.ebt())),
      Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => Array.set(Array<U32>, z, U32.from_nat(j), G.empty_blk()), G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), A2.thaw2(sa1), AS2.sla_run(l, depth, at, lo1, hd, pfa, hj)),
      Equal.cong(Array<U32>, Array<Array<U32>>, z => Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(j), z), G.empty_blk(), AR.thaw(U32, AV.ebt()), AV.ebt_thaw())),
    AS2.put_in(depth, sa1, j, AV.ebt(), hd, psa, hj))
  +c1 = Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVL(dir, z, U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), U32.sub(U32.from_nat(1n+lo1), 1), U32.from_nat(lo1), u1)
  +c2 = Equal.cong(Nat, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVL(dir, U32.from_nat(lo1), z, U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), l, u2)
  +c3 = Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVL(dir, U32.from_nat(lo1), l, z, hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), U32.sub(RM.IX(1n+lo1, hi, it, v), 1), U32.from_nat(j), u3)
  +c4 = Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo1, hi, depth, z, Array.set(Array<U32>, G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), U32.from_nat(j), G.empty_blk())), Array.set(U32, G.shl_go(l, U32.from_nat(lo1), AR.thaw(U32, it)), U32.from_nat(j), v), AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), ea)
  +c5 = Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), z), Array.set(Array<U32>, G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), U32.from_nat(j), G.empty_blk()), A2.thaw2(AT2L(lo1, hi, depth, it, at, v)), eb)
  +e1 = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVL(dir, U32.sub(U32.from_nat(1n+lo1), 1), U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), AVL(dir, U32.from_nat(lo1), U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), A2.thaw2(AT2L(lo1, hi, depth, it, at, v))), c1,
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVL(dir, U32.from_nat(lo1), U32.to_nat(U32.sub(RM.IX(1n+lo1, hi, it, v), U32.from_nat(1n+lo1))), U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), AVL(dir, U32.from_nat(lo1), l, U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), A2.thaw2(AT2L(lo1, hi, depth, it, at, v))), c2,
      Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVL(dir, U32.from_nat(lo1), l, U32.sub(RM.IX(1n+lo1, hi, it, v), 1), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), AVL(dir, U32.from_nat(lo1), l, U32.from_nat(j), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), A2.thaw2(AT2L(lo1, hi, depth, it, at, v))), c3,
        Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVL(dir, U32.from_nat(lo1), l, U32.from_nat(j), hi, depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), Array.set(Array<U32>, G.shla_go(l, U32.from_nat(lo1), A2.thaw2(at)), U32.from_nat(j), G.empty_blk())), RM.g_done(dir, lo1, hi, depth, AR.thaw(U32, IT2L(lo1, hi, depth, it, v)), A2.thaw2(AT2L(lo1, hi, depth, it, at, v))), c4, c5))))
  +sk = sub_pred(hi, lo1, hlo)
  +sl1 = Equal.trans(List<&2, U32>, AR.slots(U32, IT2L(lo1, hi, depth, it, v)), SC.update(U32, AR.slots(U32, st1), j, v), SC.update(U32, ZP.lsl(U32, False{}, 0, 0, l, AR.slots(U32, it), lo1), j, v),
    AR.upd_slots(U32, depth, st1, j, v, hj, pst),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, j, v), AR.slots(U32, st1), ZP.lsl(U32, False{}, 0, 0, l, AR.slots(U32, it), lo1), AS2.sl_slots(l, depth, it, lo1, pfi, hj)))
  +sl2 = Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, sa1), j, AV.ebt()), SC.update(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, AR.slots(AR.Tree<U32>, at), lo1), j, AV.ebt()),
    AR.upd_slots(AR.Tree<U32>, depth, sa1, j, AV.ebt(), hj, psa),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, j, AV.ebt()), AR.slots(AR.Tree<U32>, sa1), ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, AR.slots(AR.Tree<U32>, at), lo1), AS2.sla_slots(l, depth, at, lo1, pfa, hj)))
  +hw1 = Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, IT2L(lo1, hi, depth, it, v)), lo1, Nat.sub(hi, lo1)), ST.win(U32, SC.update(U32, ZP.lsl(U32, False{}, 0, 0, l, AR.slots(U32, it), lo1), j, v), lo1, 1n+k), AV.NK(1n+lo1, hi, it, v),
    Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, IT2L(lo1, hi, depth, it, v)), lo1, Nat.sub(hi, lo1)), ST.win(U32, AR.slots(U32, IT2L(lo1, hi, depth, it, v)), lo1, 1n+k), ST.win(U32, SC.update(U32, ZP.lsl(U32, False{}, 0, 0, l, AR.slots(U32, it), lo1), j, v), lo1, 1n+k),
      Equal.cong(Nat, List<&2, U32>, n => ST.win(U32, AR.slots(U32, IT2L(lo1, hi, depth, it, v)), lo1, n), Nat.sub(hi, lo1), 1n+k, sk),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => ST.win(U32, z, lo1, 1n+k), AR.slots(U32, IT2L(lo1, hi, depth, it, v)), SC.update(U32, ZP.lsl(U32, False{}, 0, 0, l, AR.slots(U32, it), lo1), j, v), sl1)),
    ZP.ins_left_win(U32, False{}, 0, 0, AR.slots(U32, it), lo1, k, l, v, hl, ED.win_fits(U32, depth, it, 1n+lo1, hi, pfi, hlo, hcap)))
  +hw2 = Equal.trans(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), lo1, Nat.sub(hi, lo1)), ST.win(AR.Tree<U32>, SC.update(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, AR.slots(AR.Tree<U32>, at), lo1), j, AV.ebt()), lo1, 1n+k), AV.NB(1n+lo1, hi, it, at, v),
    Equal.trans(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), lo1, Nat.sub(hi, lo1)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), lo1, 1n+k), ST.win(AR.Tree<U32>, SC.update(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, AR.slots(AR.Tree<U32>, at), lo1), j, AV.ebt()), lo1, 1n+k),
      Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), lo1, n), Nat.sub(hi, lo1), 1n+k, sk),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => ST.win(AR.Tree<U32>, z, lo1, 1n+k), AR.slots(AR.Tree<U32>, AT2L(lo1, hi, depth, it, at, v)), SC.update(AR.Tree<U32>, ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), l, AR.slots(AR.Tree<U32>, at), lo1), j, AV.ebt()), sl2)),
    ZP.ins_left_win(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), AR.slots(AR.Tree<U32>, at), lo1, k, l, AV.ebt(), hl, ED.win_fits(AR.Tree<U32>, depth, at, 1n+lo1, hi, pfa, hlo, hcap)))
  AV.av_new(dir, 1n+lo1, hi, depth, it, at, v, h, hv0, lo1, hi, depth, IT2L(lo1, hi, depth, it, v), AT2L(lo1, hi, depth, it, at, v), G.av_left(dir, U32.from_nat(1n+lo1), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(1n+lo1, hi, it, v), v), e1,
    sk, hw1, hw2, hk32, AR.upd_perfect(U32, depth, st1, j, v, pst), AR.upd_perfect(AR.Tree<U32>, depth, sa1, j, AV.ebt(), psa), N.le_trans(lo1, 1n+lo1, hi, N.le_succ(lo1), hlo), hcap)

def IT2R(+lo: Nat, +hi: Nat, +d: Nat, +it: AR.Tree<U32>, +v: U32) -> AR.Tree<U32>:
  AR.upd(U32, d, SH.shr_tree(Nat.sub(Nat.sub(hi, lo), AV.LV(lo, hi, it, v)), d, it, hi), Nat.add(lo, AV.LV(lo, hi, it, v)), v)

def AT2R(+lo: Nat, +hi: Nat, +d: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  AR.upd(AR.Tree<U32>, d, AS2.shra_tree(Nat.sub(Nat.sub(hi, lo), AV.LV(lo, hi, it, v)), d, at, hi), Nat.add(lo, AV.LV(lo, hi, it, v)), AV.ebt())

# ---- shifting the tail right ----

def av_right_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +hr: {Nat.is_lt(hi, SC.pow2(depth)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_right(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  +l = AV.LV(lo, hi, it, v)
  +k = Nat.sub(hi, lo)
  +i = Nat.add(lo, l)
  +m = Nat.sub(k, l)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hk32 = OP.g_depth(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, lo, hi, depth, it, at, h)
  +pfa = OP.g_adj(dir, lo, hi, depth, it, at, h)
  +hl = AV.av_hl(lo, hi, it, v)
  +hend = W.window_end(lo, hi, k, {==}, hlo)
  +hih = L.subst(Nat, z => {Nat.is_le(i, z) == True{} : Bool}, Nat.add(lo, k), hi, hend, W.add_mono(lo, l, k, hl))
  +hir = N.le_lt_trans(i, hi, SC.pow2(depth), hih, hr)
  +ri = IX.nat_round(i, depth, N.lt_le(depth, 32n, hd), hir)
  +hmh = N.le_trans(m, k, hi, H.sub_le(k, l), H.sub_le(hi, lo))
  +em = Equal.trans(Nat, Nat.sub(hi, i), Nat.sub(Nat.sub(hi, lo), l), m, Equal.sym(Nat, Nat.sub(Nat.sub(hi, lo), l), Nat.sub(hi, i), SE.sub_add_eq(hi, lo, l)), {==})
  +u = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), RM.IX(lo, hi, it, v))), U32.to_nat(U32.from_nat(Nat.sub(hi, i))), m,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(hi), RM.IX(lo, hi, it, v)), U32.from_nat(Nat.sub(hi, i)), H.sub_bridge(hi, i, 1n+depth, hk32, lt_up(hi, depth, hcap), hih)),
    Equal.trans(Nat, U32.to_nat(U32.from_nat(Nat.sub(hi, i))), U32.to_nat(U32.from_nat(m)), m,
      Equal.cong(Nat, Nat, z => U32.to_nat(U32.from_nat(z)), Nat.sub(hi, i), m, em),
      IX.nat_round(m, 1n+depth, hk32, lt_up(m, depth, N.le_trans(m, hi, SC.pow2(depth), hmh, hcap)))))
  +st1 = SH.shr_tree(m, depth, it, hi)
  +sa1 = AS2.shra_tree(m, depth, at, hi)
  +pst = BO.shr_perfect(m, depth, it, hi, pfi)
  +psa = AS2.shra_perfect(m, depth, at, hi, pfa)
  +ea = Equal.trans(Array<U32>, Array.set(U32, G.shr_go(m, U32.from_nat(hi), AR.thaw(U32, it)), U32.from_nat(i), v), Array.set(U32, AR.thaw(U32, st1), U32.from_nat(i), v), AR.thaw(U32, IT2R(lo, hi, depth, it, v)),
    Equal.cong(Array<U32>, Array<U32>, z => Array.set(U32, z, U32.from_nat(i), v), G.shr_go(m, U32.from_nat(hi), AR.thaw(U32, it)), AR.thaw(U32, st1), SH.shr_run(m, depth, it, hi, hd, pfi, hr, hmh)),
    SH.set_at(depth, st1, i, v, hd, pst, hir, ri))
  +eb = Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), U32.from_nat(i), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(i), AR.thaw(U32, AV.ebt())), A2.thaw2(AT2R(lo, hi, depth, it, at, v)),
    Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), U32.from_nat(i), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(i), G.empty_blk()), Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(i), AR.thaw(U32, AV.ebt())),
      Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => Array.set(Array<U32>, z, U32.from_nat(i), G.empty_blk()), G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), A2.thaw2(sa1), AS2.sra_run(m, depth, at, hi, hd, pfa, hr, hmh)),
      Equal.cong(Array<U32>, Array<Array<U32>>, z => Array.set(Array<U32>, A2.thaw2(sa1), U32.from_nat(i), z), G.empty_blk(), AR.thaw(U32, AV.ebt()), AV.ebt_thaw())),
    AS2.put_in(depth, sa1, i, AV.ebt(), hd, psa, hir))
  +c1 = Equal.cong(Nat, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVR(dir, lo, hi, z, U32.from_nat(i), depth, AR.thaw(U32, it), A2.thaw2(at), v), U32.to_nat(U32.sub(U32.from_nat(hi), RM.IX(lo, hi, it, v))), m, u)
  +c4 = Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo, 1n+hi, depth, z, Array.set(Array<U32>, G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), U32.from_nat(i), G.empty_blk())), Array.set(U32, G.shr_go(m, U32.from_nat(hi), AR.thaw(U32, it)), U32.from_nat(i), v), AR.thaw(U32, IT2R(lo, hi, depth, it, v)), ea)
  +c5 = Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => RM.g_done(dir, lo, 1n+hi, depth, AR.thaw(U32, IT2R(lo, hi, depth, it, v)), z), Array.set(Array<U32>, G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), U32.from_nat(i), G.empty_blk()), A2.thaw2(AT2R(lo, hi, depth, it, at, v)), eb)
  +e1 = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVR(dir, lo, hi, U32.to_nat(U32.sub(U32.from_nat(hi), RM.IX(lo, hi, it, v))), U32.from_nat(i), depth, AR.thaw(U32, it), A2.thaw2(at), v), AVR(dir, lo, hi, m, U32.from_nat(i), depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo, 1n+hi, depth, AR.thaw(U32, IT2R(lo, hi, depth, it, v)), A2.thaw2(AT2R(lo, hi, depth, it, at, v))), c1,
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVR(dir, lo, hi, m, U32.from_nat(i), depth, AR.thaw(U32, it), A2.thaw2(at), v), RM.g_done(dir, lo, 1n+hi, depth, AR.thaw(U32, IT2R(lo, hi, depth, it, v)), Array.set(Array<U32>, G.shra_go(m, U32.from_nat(hi), A2.thaw2(at)), U32.from_nat(i), G.empty_blk())), RM.g_done(dir, lo, 1n+hi, depth, AR.thaw(U32, IT2R(lo, hi, depth, it, v)), A2.thaw2(AT2R(lo, hi, depth, it, at, v))), c4, c5))
  +sk = BO.sub_succ_l(hi, lo, hlo)
  +hkl = L.subst(Nat, z => {Nat.is_lt(z, SC.length(U32, AR.slots(U32, it))) == True{} : Bool}, hi, Nat.add(lo, k), Equal.sym(Nat, Nat.add(lo, k), hi, hend), L.subst(Nat, z => {Nat.is_lt(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, AR.slots(U32, it)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, it)), SC.pow2(depth), AR.slots_length(U32, depth, it, pfi)), hr))
  +hkb = L.subst(Nat, z => {Nat.is_lt(z, SC.length(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at))) == True{} : Bool}, hi, Nat.add(lo, k), Equal.sym(Nat, Nat.add(lo, k), hi, hend), L.subst(Nat, z => {Nat.is_lt(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at)), Equal.sym(Nat, SC.length(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at)), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pfa)), hr))
  +sl1 = Equal.trans(List<&2, U32>, AR.slots(U32, IT2R(lo, hi, depth, it, v)), SC.update(U32, AR.slots(U32, st1), i, v), SC.update(U32, ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)), i, v),
    AR.upd_slots(U32, depth, st1, i, v, hir, pst),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, i, v), AR.slots(U32, st1), ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)),
      Equal.trans(List<&2, U32>, AR.slots(U32, st1), ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), hi), ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)),
        AS2.sr_slots(m, depth, it, hi, pfi, hr, hmh),
        Equal.cong(Nat, List<&2, U32>, n => ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), n), hi, Nat.add(lo, k), Equal.sym(Nat, Nat.add(lo, k), hi, hend)))))
  +sl2 = Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, sa1), i, AV.ebt()), SC.update(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)), i, AV.ebt()),
    AR.upd_slots(AR.Tree<U32>, depth, sa1, i, AV.ebt(), hir, psa),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, i, AV.ebt()), AR.slots(AR.Tree<U32>, sa1), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)),
      Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, sa1), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), hi), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)),
        AS2.sra_slots(m, depth, at, hi, pfa, hr, hmh),
        Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), n), hi, Nat.add(lo, k), Equal.sym(Nat, Nat.add(lo, k), hi, hend)))))
  +hw1 = Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, IT2R(lo, hi, depth, it, v)), lo, Nat.sub(1n+hi, lo)), ST.win(U32, SC.update(U32, ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)), i, v), lo, 1n+k), AV.NK(lo, hi, it, v),
    Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, IT2R(lo, hi, depth, it, v)), lo, Nat.sub(1n+hi, lo)), ST.win(U32, AR.slots(U32, IT2R(lo, hi, depth, it, v)), lo, 1n+k), ST.win(U32, SC.update(U32, ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)), i, v), lo, 1n+k),
      Equal.cong(Nat, List<&2, U32>, n => ST.win(U32, AR.slots(U32, IT2R(lo, hi, depth, it, v)), lo, n), Nat.sub(1n+hi, lo), 1n+k, sk),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => ST.win(U32, z, lo, 1n+k), AR.slots(U32, IT2R(lo, hi, depth, it, v)), SC.update(U32, ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, it), Nat.add(lo, k)), i, v), sl1)),
    ZP.ins_right_win(U32, False{}, 0, 0, AR.slots(U32, it), lo, k, l, v, hl, hkl))
  +hw2 = Equal.trans(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), lo, Nat.sub(1n+hi, lo)), ST.win(AR.Tree<U32>, SC.update(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)), i, AV.ebt()), lo, 1n+k), AV.NB(lo, hi, it, at, v),
    Equal.trans(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), lo, Nat.sub(1n+hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), lo, 1n+k), ST.win(AR.Tree<U32>, SC.update(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)), i, AV.ebt()), lo, 1n+k),
      Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), lo, n), Nat.sub(1n+hi, lo), 1n+k, sk),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => ST.win(AR.Tree<U32>, z, lo, 1n+k), AR.slots(AR.Tree<U32>, AT2R(lo, hi, depth, it, at, v)), SC.update(AR.Tree<U32>, ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, at), Nat.add(lo, k)), i, AV.ebt()), sl2)),
    ZP.ins_right_win(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), AR.slots(AR.Tree<U32>, at), lo, k, l, AV.ebt(), hl, hkb))
  AV.av_new(dir, lo, hi, depth, it, at, v, h, hv0, lo, 1n+hi, depth, IT2R(lo, hi, depth, it, v), AT2R(lo, hi, depth, it, at, v), G.av_right(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), e1,
    sk, hw1, hw2, hk32, AR.upd_perfect(U32, depth, st1, i, v, pst), AR.upd_perfect(AR.Tree<U32>, depth, sa1, i, AV.ebt(), psa), N.le_trans(lo, hi, 1n+hi, hlo, N.le_succ(hi)), N.lt_succ_le_succ(hi, SC.pow2(depth), hr))
