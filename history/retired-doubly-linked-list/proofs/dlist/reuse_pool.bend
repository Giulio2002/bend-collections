import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/doubly_linked_list.bend as D
import ./state.bend as ST
import ./facts.bend as F
import ./core.bend as K
import ./items.bend as IT
import ./tolist.bend as TL
import ./links.bend as LK
import ./split.bend as SP
import ./mu0.bend as MU0
import ./retarget.bend as RT
import ./tset.bend as TS
import ./insitems.bend as II
import ./reuse_insert.bend as RI
import ./free_chain.bend as FC
import ./free_facts.bend as FF

# The FULL live + free-pool invariant survives insertion at a retired slot.
# This includes disjointness, free-chain links and count conservation, not
# just the visible live sequence.
def after(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +v: T) -> FC.Shadow<T>:
  FC.Pool{RI.lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free}

def conserved(+x: List<&2, Nat>, +y: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +fresh: Nat, +h: {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, x, y)), SC.length(Nat, Con{idx, free})), fresh) == True{} : Bool}) -> {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, x, Con{idx, y})), SC.length(Nat, free)), fresh) == True{} : Bool}:
  +n = SC.length(Nat, SC.append(Nat, x, y))
  +f = SC.length(Nat, free)
  %II.cnt_ins(x, idx, y) : {Nat.is_eq(Nat.add(_, f), fresh) == True{} : Bool}
  %N.add_succ(n, f) : {Nat.is_eq(_, fresh) == True{} : Bool}
  h

def good(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +v: T, +g: {FC.good(~T, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}, Con{idx, free}}) == True{} : Bool}) -> {FC.good(~T, after(~T, tag, fresh, depth, tv, tp, tn, x, y, idx, free, v)) == True{} : Bool}:
  +ord = SC.append(Nat, x, y)
  +out = SC.append(Nat, x, Con{idx, y})
  +lg = FF.live(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)
  +fb = FF.bounds(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)
  +fi = IT.lt_head(idx, free, fresh, fb)
  +fr = N.lt_le_trans(idx, fresh, SC.pow2(depth), fi, F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, lg))
  +nd = FF.nodup(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)
  +notfree = MU0.not_true(ST.lmem(idx, free), L.and_left(Bool.not(ST.lmem(idx, free)), ST.nodup(free), nd))
  +dj = FF.disjoint(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)
  +member = L.subst(Bool, z => {Bool.or(z, ST.lmem(idx, free)) == True{} : Bool}, True{}, Nat.is_eq(idx, idx), Equal.sym(Bool, Nat.is_eq(idx, idx), True{}, N.is_eq_refl(idx)), {==})
  +notlive = SP.disj_mem(ord, Con{idx, free}, idx, dj, member)
  +djtail = FC.disjoint_drop(ord, idx, free, dj)
  +ns = AR.slots(U32, tn)
  +alllinks = FF.links(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)
  +tail_links = L.and_right(U32.is_eq(ST.lat(ns, idx), ST.hd(free)), FC.links(free, ns), alllinks)
  +b = ST.hd_or(y, D.nil())
  +lf = ST.ln(idx)
  +tn1 = AR.upd(U32, depth, tn, idx, b)
  +tn2 = TS.tnup(depth, tn1, x, lf)
  +pf = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, lg)
  +lo = K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, lg), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, lg))
  +ens = Equal.trans(List<&2, U32>, AR.slots(U32, tn2), RT.nupd(AR.slots(U32, tn1), x, lf), RT.nupd(SC.update(U32, ns, idx, b), x, lf), TS.tnup_slots(depth, tn1, x, lf, AR.upd_perfect(U32, depth, tn, idx, b, pf), TL.alllt_l(x, y, SC.pow2(depth), lo)), Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(z, x, lf), AR.slots(U32, tn1), SC.update(U32, ns, idx, b), AR.upd_slots(U32, depth, tn, idx, b, fr, pf)))
  +flinks = L.subst(List<&2, U32>, z => {FC.links(free, z) == True{} : Bool}, RT.nupd(SC.update(U32, ns, idx, b), x, lf), AR.slots(U32, tn2), Equal.sym(List<&2, U32>, AR.slots(U32, tn2), RT.nupd(SC.update(U32, ns, idx, b), x, lf), ens), FC.reuse_links(free, ns, idx, b, x, notfree, FC.disjoint_prefix(x, y, free, djtail), tail_links))
  FF.make(~T, tag, fresh, depth, AR.upd(Maybe<&2, T>, depth, tv, idx, Some{v}), TS.tpup(depth, AR.upd(U32, depth, tp, idx, LK.lastl(x, D.nil())), y, lf), tn2, out, free,
    RI.li_good(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v, lg, fr, fi, notlive),
    IT.lt_tail(idx, free, fresh, fb), L.and_right(Bool.not(ST.lmem(idx, free)), ST.nodup(free), nd), FC.disjoint_insert(x, y, idx, free, notfree, djtail), flinks,
    conserved(x, y, idx, free, fresh, FF.count(~T, tag, fresh, depth, tv, tp, tn, ord, Con{idx, free}, g)))
