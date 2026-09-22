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
import ./reuse_retire.bend as SELF

def stamp_model_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32) -> {ST.model(~U32, SELF.stamp(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free)) == ST.model(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) : DS.Model<U32>}:
  SELF.stamp_model(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free)

def stamp_good_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}, +dead: {ST.lmem(i, ord) == False{} : Bool}) -> {ST.good(~U32, SELF.stamp(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free)) == True{} : Bool}:
  SELF.stamp_good(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free, h, hi, dead)

def mark_real_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}) -> {SELF.mark(~U32, ST.real(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), U32.from_nat(i), free) == RI.real_with_free(~U32, SELF.stamp(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free), D.link(U32.from_nat(i))) : D.DList<U32>}:
  SELF.mark_real(~U32, tag, fresh, depth, tv, tp, tn, ord, i, free, h, hi)

def recycling_removal_u32(+tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, +tv: AR.Tree<Maybe<&2, U32>>, +i: U32, +v: U32, +tp: AR.Tree<U32>, +p: U32, +tn: AR.Tree<U32>, +n: U32) -> {D.rmf_links(~U32, tag, fresh, free, count, head, tail, depth, cap, AR.thaw(Maybe<&2, U32>, tv), i, v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n)) == SELF.mark_result(~U32, i, free, D.rm_links(~U32, tag, fresh, 0, count, head, tail, depth, cap, AR.thaw(Maybe<&2, U32>, tv), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n))) : D.DList<U32> & Maybe<&2, U32>}:
  SELF.recycling_removal(~U32, tag, fresh, free, count, head, tail, depth, cap, tv, i, v, tp, p, tn, n)

def stamp_model_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32) -> {ST.model(~String, SELF.stamp(~String, tag, fresh, depth, tv, tp, tn, ord, i, free)) == ST.model(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) : DS.Model<String>}:
  SELF.stamp_model(~String, tag, fresh, depth, tv, tp, tn, ord, i, free)

def stamp_good_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}, +dead: {ST.lmem(i, ord) == False{} : Bool}) -> {ST.good(~String, SELF.stamp(~String, tag, fresh, depth, tv, tp, tn, ord, i, free)) == True{} : Bool}:
  SELF.stamp_good(~String, tag, fresh, depth, tv, tp, tn, ord, i, free, h, hi, dead)

def mark_real_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: Nat, +free: U32, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(depth)) == True{} : Bool}) -> {SELF.mark(~String, ST.real(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), U32.from_nat(i), free) == RI.real_with_free(~String, SELF.stamp(~String, tag, fresh, depth, tv, tp, tn, ord, i, free), D.link(U32.from_nat(i))) : D.DList<String>}:
  SELF.mark_real(~String, tag, fresh, depth, tv, tp, tn, ord, i, free, h, hi)

def recycling_removal_string(+tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, +tv: AR.Tree<Maybe<&2, String>>, +i: U32, +v: String, +tp: AR.Tree<U32>, +p: U32, +tn: AR.Tree<U32>, +n: U32) -> {D.rmf_links(~String, tag, fresh, free, count, head, tail, depth, cap, AR.thaw(Maybe<&2, String>, tv), i, v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n)) == SELF.mark_result(~String, i, free, D.rm_links(~String, tag, fresh, 0, count, head, tail, depth, cap, AR.thaw(Maybe<&2, String>, tv), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), n))) : D.DList<String> & Maybe<&2, String>}:
  SELF.recycling_removal(~String, tag, fresh, free, count, head, tail, depth, cap, tv, i, v, tp, p, tn, n)

