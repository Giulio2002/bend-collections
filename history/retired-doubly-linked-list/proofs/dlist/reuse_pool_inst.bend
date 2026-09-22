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
import ./reuse_pool.bend as R

def good_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +v: U32, +g: {FC.good(~U32, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}, Con{idx, free}}) == True{} : Bool}) -> {FC.good(~U32, R.after(~U32, tag, fresh, depth, tv, tp, tn, x, y, idx, free, v)) == True{} : Bool}:
  R.good(~U32, tag, fresh, depth, tv, tp, tn, x, y, idx, free, v, g)

def good_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +idx: Nat, +free: List<&2, Nat>, +v: String, +g: {FC.good(~String, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}, Con{idx, free}}) == True{} : Bool}) -> {FC.good(~String, R.after(~String, tag, fresh, depth, tv, tp, tn, x, y, idx, free, v)) == True{} : Bool}:
  R.good(~String, tag, fresh, depth, tv, tp, tn, x, y, idx, free, v, g)

