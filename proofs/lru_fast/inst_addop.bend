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
import ./table.bend as TB
import ./insert.bend as INS
import ./addfacts.bend as AF
import ./remove.bend as RM
import ./addop.bend as AO
import ./simple.bend as SI

def insf_real_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, e: F.Slot<U32>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {F.insert_new(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, e) == ST.real(~U32, AO.ins_fl(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e)) : F.Fast<U32>}:
  AO.insf_real(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e, h, q, hq, hcq, hroom)

def insf_inv_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, +e: F.Slot<U32>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +hno: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +ho: {ST.is_occ(U32, e) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {ST.good(~U32, AO.ins_fl(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e)) == True{} : Bool}:
  AO.insf_inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e, h, hno, ho, q, hq, hcq, hroom)

def insf_model_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, +v: U32, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {ST.model(~U32, AO.ins_fl(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~U32, life, v, now))) == S.LM{cap, life, S.snoc(U32, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))} : S.Model<U32>}:
  AO.insf_model(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq, hroom)

def room_of_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == False{} : Bool}) -> {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}:
  AO.room_of(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, ef)

def add_real_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: U32, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {F.add(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, v, F.int_stamp(now)) == AO.apb(~U32, AO.ad_ghost(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : F.Fast<U32> & Bool}:
  AO.add_real(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)

def add_inv_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: U32, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {AO.gpb(~U32, AO.ad_ghost(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) == True{} : Bool}:
  AO.add_inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)

def add_model_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: U32, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {S.add_found(U32, cap, life, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(U32, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord), key)) == AO.mpb(~U32, AO.ad_ghost(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : S.Model<U32> & E.Obs<U32>}:
  AO.add_model(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)


def metrics_real_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.metrics(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ST.mets(AR.slots(U32, tc))) : F.Fast<U32> & T.Metrics}:
  SI.metrics_real(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def len_obs_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {U32.from_nat(SC.length(Nat, ord)) == U32.from_nat(S.len(U32, ST.ents(U32, AR.slots(String, tk), AR.slots(F.Slot<U32>, te), ord))) : U32}:
  SI.len_obs(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def purge_real_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>) -> {F.purge(~U32, ST.real(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (ST.real(~U32, SI.pg_sh(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn)), U32.from_nat(SC.length(Nat, ord))) : F.Fast<U32> & U32}:
  SI.purge_real(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl)

def purge_inv_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~U32, SI.pg_sh(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn)) == True{} : Bool}:
  SI.purge_inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def purge_model_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>) -> {ST.model(~U32, SI.pg_sh(U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn)) == S.LM{cap, life, Nil{}, T.zero_metrics()} : S.Model<U32>}:
  SI.purge_model(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn)
