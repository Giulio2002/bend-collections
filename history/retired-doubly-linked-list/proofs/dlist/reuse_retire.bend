import Base
import ../lib/u32.bend as U
import ../lib/logic.bend as L
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./reuse_insert.bend as RI
import ./insert.bend as IN

# Store a free-chain link in a retired slot's next field. Neither the
# live sequence nor its DLL invariant may change.
def stamp(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32) -> ST.Shadow<T>:
  ST.Sh{tag, fresh, depth, tv, tp, AR.upd(U32, depth, tn, i, free), ord}

def stamp_model(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32) -> {ST.model(~T, stamp(~T, tag, fresh, depth, tv, tp, tn, ord, i, free)) == ST.model(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) : DS.Model<T>}:
  {==}

def stamp_good(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}, +dead: {ST.lmem(i, ord) == False{} : Bool}) -> {ST.good(~T, stamp(~T, tag, fresh, depth, tv, tp, tn, ord, i, free)) == True{} : Bool}:
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +pf = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +eq = Equal.trans(Bool, ST.lk(ord, D.nil(), D.nil(), ps, AR.slots(U32, AR.upd(U32, depth, tn, i, free))), ST.lk(ord, D.nil(), D.nil(), ps, SC.update(U32, ns, i, free)), ST.lk(ord, D.nil(), D.nil(), ps, ns), Equal.cong(List<&2, U32>, Bool, z => ST.lk(ord, D.nil(), D.nil(), ps, z), AR.slots(U32, AR.upd(U32, depth, tn, i, free)), SC.update(U32, ns, i, free), AR.upd_slots(U32, depth, tn, i, free, hi, pf)), LK.lk_frame_n(ord, D.nil(), D.nil(), ps, ns, i, free, dead))
  +links = Equal.trans(Bool, ST.lk(ord, D.nil(), D.nil(), ps, AR.slots(U32, AR.upd(U32, depth, tn, i, free))), ST.lk(ord, D.nil(), D.nil(), ps, ns), True{}, eq, F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  F.good_mk(~T, tag, fresh, depth, tv, tp, AR.upd(U32, depth, tn, i, free), ord, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h), AR.upd_perfect(U32, depth, tn, i, free, pf), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h), links)

def mark(~T: Data, s: D.DList<T>, +i: U32, +free: U32) -> D.DList<T>:
  D.DL{tag, fresh, oldfree, count, head, tail, depth, cap, vals, prevs, nexts} = s
  D.DL{tag, fresh, D.link(i), count, head, tail, depth, cap, vals, prevs, Array.set(U32, nexts, i, free)}

def mark_real(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}) -> {mark(~T, ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), U32.from_nat(i), free) == RI.real_with_free(~T, stamp(~T, tag, fresh, depth, tv, tp, tn, ord, i, free), D.link(U32.from_nat(i))) : D.DList<T>}:
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tn), U32.from_nat(i), free), AR.thaw(U32, AR.upd(U32, depth, tn, i, free)), IN.set_f(U32, depth, tn, i, free, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi, F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h))) : {D.DL{tag, U32.from_nat(fresh), D.link(U32.from_nat(i)), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), _} == RI.real_with_free(~T, stamp(~T, tag, fresh, depth, tv, tp, tn, ord, i, free), D.link(U32.from_nat(i))) : D.DList<T>}
  {==}

# Recycling removal is the already-proven splice/removal, followed by putting
# the retired slot onto the free chain. This equation is about the runtime.
def mark_result(~T: Data, +i: U32, +free: U32, r: D.DList<T> & Result<&2, &2, E.Error, T>) -> D.DList<T> & Maybe<&2, T>:
  match r:
    case Tuple{s, Done{v}}:
      (mark(~T, s, i, free), Some{v})
    case Tuple{s, Fail{e}}:
      (s, None{})

def recycling_removal(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, +tv: AR.Tree<Maybe<&2, T>>, +i: U32, +v: T, +tp: AR.Tree<U32>, +p: U32, +tn: AR.Tree<U32>, +n: U32) -> {D.rmf_links(~T, tag, fresh, free, count, head, tail, depth, cap, AR.thaw(Maybe<&2, T>, tv), i, v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n)) == mark_result(~T, i, free, D.rm_links(~T, tag, fresh, 0, count, head, tail, depth, cap, AR.thaw(Maybe<&2, T>, tv), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n))) : D.DList<T> & Maybe<&2, T>}:
  {==}
