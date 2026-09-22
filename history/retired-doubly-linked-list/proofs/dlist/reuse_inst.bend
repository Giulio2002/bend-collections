import Base
import ./insert.bend as IN
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../graph/ashift.bend as AS2
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./core.bend as K
import ./alive.bend as AL
import ./reads.bend as RD
import ./nbrs.bend as NB
import ./mu0.bend as MU0
import ./split.bend as SP
import ./retarget.bend as RT
import ./rmfacts.bend as RF
import ./tset.bend as TS
import ./mut.bend as MU
import ./tolist.bend as TL
import ../graph/zip.bend as ZP
import ./insfacts.bend as IF
import ./inslk.bend as IL
import ./insitems.bend as II
import ./reuse_facts.bend as RF2
import ./reuse_insert.bend as R

def li_good_u32(+tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.good(~U32, R.lsh(~U32, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == True{} : Bool}:
  R.li_good(~U32, tag, fresh, idx, depth, tv, tp, tn, x, y, v, h, hr, hidx, hfree)

def li_model_u32(+tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.model(~U32, R.lsh(~U32, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == DS.DM{tag, fresh, SC.append(E.Item<U32>, ST.items(U32, AR.slots(Maybe<&2, U32>, tv), x), Con{E.Item{U32.from_nat(idx), v}, ST.items(U32, AR.slots(Maybe<&2, U32>, tv), y)})} : DS.Model<U32>}:
  R.li_model(~U32, tag, fresh, idx, depth, tv, tp, tn, x, y, v, h, hr, hidx, hfree)

def li_rt_u32(+tag: U32, +fresh: Nat, +idx: Nat, +free: U32, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}) -> {D.link_in(~U32, tag, U32.from_nat(idx), U32.from_nat(fresh), free, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, U32>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v) == (R.real_with_free(~U32, R.lsh(~U32, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, U32.from_nat(idx)}) : D.DList<U32> & E.Handle}:
  R.li_rt(~U32, tag, fresh, idx, free, depth, tv, tp, tn, x, y, v, h, hr)

def li_good_string(+tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: String, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.good(~String, R.lsh(~String, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == True{} : Bool}:
  R.li_good(~String, tag, fresh, idx, depth, tv, tp, tn, x, y, v, h, hr, hidx, hfree)

def li_model_string(+tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: String, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.model(~String, R.lsh(~String, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == DS.DM{tag, fresh, SC.append(E.Item<String>, ST.items(String, AR.slots(Maybe<&2, String>, tv), x), Con{E.Item{U32.from_nat(idx), v}, ST.items(String, AR.slots(Maybe<&2, String>, tv), y)})} : DS.Model<String>}:
  R.li_model(~String, tag, fresh, idx, depth, tv, tp, tn, x, y, v, h, hr, hidx, hfree)

def li_rt_string(+tag: U32, +fresh: Nat, +idx: Nat, +free: U32, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: String, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}) -> {D.link_in(~String, tag, U32.from_nat(idx), U32.from_nat(fresh), free, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, String>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v) == (R.real_with_free(~String, R.lsh(~String, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, U32.from_nat(idx)}) : D.DList<String> & E.Handle}:
  R.li_rt(~String, tag, fresh, idx, free, depth, tv, tp, tn, x, y, v, h, hr)

