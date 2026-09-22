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
import ./retire_pool.bend as R

def good_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +free: List<&2, Nat>, +v: U32, +g: {FC.good(~U32, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, free}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~U32, tv, i) == Some{v} : Maybe<&2, U32>}) -> {FC.good(~U32, R.after(~U32, tag, fresh, depth, tv, tp, tn, a, b, i, free)) == True{} : Bool}:
  R.good(~U32, tag, fresh, depth, tv, tp, tn, a, b, i, free, v, g, hi, em)

def good_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +free: List<&2, Nat>, +v: String, +g: {FC.good(~String, FC.Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, free}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~String, tv, i) == Some{v} : Maybe<&2, String>}) -> {FC.good(~String, R.after(~String, tag, fresh, depth, tv, tp, tn, a, b, i, free)) == True{} : Bool}:
  R.good(~String, tag, fresh, depth, tv, tp, tn, a, b, i, free, v, g, hi, em)

