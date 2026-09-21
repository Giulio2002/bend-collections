import Base
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import ../dlist/state.bend as DST
import ./state.bend as ST
import ./keys.bend as KY

def ex_con_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: F.Stamp, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {F.ex_head(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now) == F.ex_slot(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, ST.sat(U32, AR.slots(F.Slot<U32>, te), s0)) : F.Fast<U32> & Bool}:
  KY.ex_con(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, h)

def st_real_u32(fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.exp_go(~U32, fuel, F.int_stamp(now), (ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})) == ST.real(~U32, KY.st_g(U32, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : F.Fast<U32>}:
  KY.st_real(~U32, fuel, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h)

def st_model_u32(fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.keys_fin(U32, cap, life, S.strip(U32, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord), ST.mets(AR.slots(U32, tc)), now)) == KY.kobs(~U32, KY.st_g(U32, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : S.Model<U32> & E.Obs<U32>}:
  KY.st_model(~U32, fuel, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h)

def st_inv_u32(fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~U32, KY.st_g(U32, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) == True{} : Bool}:
  KY.st_inv(~U32, fuel, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h)

def klist_ok_u32(sh: ST.Shadow<U32>, +h: {ST.good(~U32, sh) == True{} : Bool}) -> {F.obs_keys(~U32, F.keys_list(~U32, ST.real(~U32, sh))) == (ST.real(~U32, sh), E.OKeys{S.keys(U32, KY.ents_of(U32, sh))}) : F.Fast<U32> & E.Obs<U32>}:
  KY.klist_ok(~U32, sh, h)

