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
import ./steps.bend as SP

def len_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Len{}):
  SP.len_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def cap_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Capacity{}):
  SP.cap_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def life_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +ns: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.SetLifetime{ns}):
  SP.life_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, ns, h)

def metrics_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Metrics{}):
  SP.metrics_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def purge_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Purge{}):
  SP.purge_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)

def remove_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Remove{key}):
  SP.remove_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, h)

def get_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Get{key, now}):
  SP.get_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)

def peek_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Peek{key, now}):
  SP.peek_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)

def contains_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Contains{key, now}):
  SP.contains_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)

def add_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: U32, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Add{key, v, now}):
  SP.add_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)

def resize_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Resize{c}):
  SP.resize_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, h)

def keys_ok_u32(+cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +h: {ST.inv(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> SP.StepOK(~U32, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Keys{now}):
  SP.keys_ok(~U32, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, h)

