import Base
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import ./state.bend as ST
import ./resize.bend as RZ
import support/links_split.bend as SP

def sr_real_u32(fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +j: Nat, +h: {ST.inv(~U32, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.shrink(~U32, fuel, capn, F.SR{ST.real(~U32, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(j)}) == RZ.srp(~U32, RZ.sr_g(U32, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), j) : F.Shr<U32>}:
  RZ.sr_real(~U32, fuel, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, j, h)

def hrm_ents_u32(+c0: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, AR.upd(F.Slot<U32>, depth, te, s0, F.Vacant{})), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))) == S.tail(U32, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), Con{s0, rest})) : List<&2, S.Ent<U32>>}:
  RZ.hrm_ents(~U32, c0, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h)

def sr_model_u32(fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, fuel) == True{} : Bool}, +h: {ST.inv(~U32, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RZ.sr_mp(~U32, RZ.sr_g(U32, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (S.LM{capn, life, S.dropn(U32, k, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<U32> & Nat}:
  RZ.sr_model(~U32, fuel, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, h)

def sr_inv_u32(fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, fuel) == True{} : Bool}, +hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool}, +h: {ST.inv(~U32, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RZ.sr_gd(~U32, RZ.sr_g(U32, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == True{} : Bool}:
  RZ.sr_inv(~U32, fuel, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, hc, h)
