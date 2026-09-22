import Base
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
import ./cut_live.bend as C

def cut_u32(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~U32, tv, i) == Some{v} : Maybe<&2, U32>}) -> {C.RML(~U32, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, U32>, AR.thaw(Maybe<&2, U32>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)) == (ST.real(~U32, C.shadow(~U32, tag, fresh, depth, tv, tp, tn, a, b, i)), E.OVal{Done{v}}) : D.DList<U32> & E.Obs<U32>} & ({ST.good(~U32, C.shadow(~U32, tag, fresh, depth, tv, tp, tn, a, b, i)) == True{} : Bool} & {ST.items(U32, AR.slots(Maybe<&2, U32>, AR.upd(Maybe<&2, U32>, depth, tv, U32.to_nat(i), None{})), SC.append(Nat, a, b)) == DS.del(U32, ST.items(U32, AR.slots(Maybe<&2, U32>, tv), SC.append(Nat, a, Con{U32.to_nat(i), b})), i) : List<&2, E.Item<U32>>}):
  C.cut(~U32, tag, fresh, depth, tv, tp, tn, a, b, i, v, h, hi, em)

def cut_string(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, String>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +v: String, +h: {ST.good(~String, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~String, tv, i) == Some{v} : Maybe<&2, String>}) -> {C.RML(~String, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, String>, AR.thaw(Maybe<&2, String>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)) == (ST.real(~String, C.shadow(~String, tag, fresh, depth, tv, tp, tn, a, b, i)), E.OVal{Done{v}}) : D.DList<String> & E.Obs<String>} & ({ST.good(~String, C.shadow(~String, tag, fresh, depth, tv, tp, tn, a, b, i)) == True{} : Bool} & {ST.items(String, AR.slots(Maybe<&2, String>, AR.upd(Maybe<&2, String>, depth, tv, U32.to_nat(i), None{})), SC.append(Nat, a, b)) == DS.del(String, ST.items(String, AR.slots(Maybe<&2, String>, tv), SC.append(Nat, a, Con{U32.to_nat(i), b})), i) : List<&2, E.Item<String>>}):
  C.cut(~String, tag, fresh, depth, tv, tp, tn, a, b, i, v, h, hi, em)

