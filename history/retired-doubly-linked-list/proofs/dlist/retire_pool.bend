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
import ./reads.bend as RD
import ./links.bend as LK
import ./split.bend as SP
import ./retarget.bend as RT
import ./rmfacts.bend as RF
import ./tset.bend as TS
import ./insitems.bend as II
import ./reuse_facts.bend as RIF
import ./reuse_retire.bend as RR
import ./cut_live.bend as C
import ./free_chain.bend as FC
import ./free_facts.bend as FF

# Retire a live slot after the checked unlink operation. The new free chain
# is exactly this slot followed by the previous chain.
def after(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +free: List<&2, Nat>) -> FC.Shadow<T>:
  FC.Pool{RR.stamp(~T, tag, fresh, depth, AR.upd(Maybe<&2, T>, depth, tv, U32.to_nat(i), None{}), TS.tpup(depth, tp, b, LK.lastl(a, D.nil())), TS.tnup(depth, tn, a, ST.hd_or(b, D.nil())), SC.append(Nat, a, b), U32.to_nat(i), ST.hd(free)), Con{U32.to_nat(i), free}}

def conserved(+a: List<&2, Nat>, +b: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +fresh: Nat, +h: {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, a, Con{idx, b})), SC.length(Nat, free)), fresh) == True{} : Bool}) -> {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, a, b)), SC.length(Nat, Con{idx, free})), fresh) == True{} : Bool}:
  +n = SC.length(Nat, SC.append(Nat, a, b))
  +f = SC.length(Nat, free)
  %Equal.sym(Nat, Nat.add(n, 1n+f), 1n+Nat.add(n, f), N.add_succ(n, f)) : {Nat.is_eq(_, fresh) == True{} : Bool}
  %Equal.sym(Nat, 1n+n, SC.length(Nat, SC.append(Nat, a, Con{idx, b})), II.cnt_ins(a, idx, b)) : {Nat.is_eq(Nat.add(_, f), fresh) == True{} : Bool}
  h

def good(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +free: List<&2, Nat>, +v: T, +g: {FC.good(~T, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, free}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}) -> {FC.good(~T, after(~T, tag, fresh, depth, tv, tp, tn, a, b, i, free)) == True{} : Bool}:
  +idx = U32.to_nat(i)
  +ord = SC.append(Nat, a, Con{idx, b})
  +out = SC.append(Nat, a, b)
  +lg = FF.live(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)
  +hr = N.lt_le_trans(idx, fresh, SC.pow2(depth), hi, F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, lg))
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, idx, None{})
  +tp2 = TS.tpup(depth, tp, b, LK.lastl(a, D.nil()))
  +q = ST.hd_or(b, D.nil())
  +tn2 = TS.tnup(depth, tn, a, q)
  +ns = AR.slots(U32, tn)
  +pf = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, lg)
  +lo = K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, lg), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, lg))
  +pa = TL.alllt_l(a, Con{idx, b}, SC.pow2(depth), lo)
  +pf2 = TS.tnup_pf(depth, tn, a, q, pf)
  +dj = FF.disjoint(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)
  +notfree = SP.disj_mem(free, ord, idx, RF.disj_flip(ord, free, dj), RIF.inserted_member(a, b, idx))
  +dead = FC.removed_absent(a, idx, b, F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, lg))
  +cutg = C.cut_good(~T, tag, fresh, depth, tv, tp, tn, a, b, i, v, lg, hi, em)
  +ens = TS.tnup_slots(depth, tn, a, q, pf, pa)
  +links2 = L.subst(List<&2, U32>, z => {FC.links(free, z) == True{} : Bool}, RT.nupd(ns, a, q), AR.slots(U32, tn2), Equal.sym(List<&2, U32>, AR.slots(U32, tn2), RT.nupd(ns, a, q), ens), Equal.trans(Bool, FC.links(free, RT.nupd(ns, a, q)), FC.links(free, ns), True{}, FC.frame_live_tail(free, ns, a, q, FC.disjoint_prefix(a, Con{idx, b}, free, dj)), FF.links(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)))
  +hlen = AR.len_lt(U32, depth, tn2, idx, pf2, hr)
  +flinks = L.subst(List<&2, U32>, z => {FC.links(Con{idx, free}, z) == True{} : Bool}, SC.update(U32, AR.slots(U32, tn2), idx, ST.hd(free)), AR.slots(U32, AR.upd(U32, depth, tn2, idx, ST.hd(free))), Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, depth, tn2, idx, ST.hd(free))), SC.update(U32, AR.slots(U32, tn2), idx, ST.hd(free)), AR.upd_slots(U32, depth, tn2, idx, ST.hd(free), hr, pf2)), FC.prepend(free, AR.slots(U32, tn2), idx, notfree, hlen, links2))
  +notf = L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(idx, free), Equal.sym(Bool, ST.lmem(idx, free), False{}, notfree), {==})
  +notout = L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(idx, out), Equal.sym(Bool, ST.lmem(idx, out), False{}, dead), {==})
  +djnew = RF.disj_flip(Con{idx, free}, out, L.and_intro(Bool.not(ST.lmem(idx, out)), SP.disj(free, out), notout, RF.disj_flip(out, free, FC.disjoint_cut(a, idx, b, free, dj))))
  FF.make(~T, tag, fresh, depth, tv2, tp2, AR.upd(U32, depth, tn2, idx, ST.hd(free)), out, Con{idx, free}, RR.stamp_good(~T, tag, fresh, depth, tv2, tp2, tn2, out, idx, ST.hd(free), cutg, hr, dead), L.and_intro(Nat.is_lt(idx, fresh), ST.alllt(free, fresh), hi, FF.bounds(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)), L.and_intro(Bool.not(ST.lmem(idx, free)), ST.nodup(free), notf, FF.nodup(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)), djnew, flinks, conserved(a, b, idx, free, fresh, FF.count(~T, tag, fresh, depth, tv, tp, tn, ord, free, g)))
