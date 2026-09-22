import Base
import ../../spec/common.bend as SC
import ../../types/lru_fast.bend as E
import ./trace.bend as TR

def trace_new_u32(+cap: U32, +ops: List<&2, E.Op<U32>>, +hc0: {U32.is_eq(cap, 0) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hops: {TR.all_ok(U32, q, ops) == True{} : Bool}) -> TR.TraceNew(~U32, cap, ops):
  TR.trace_new(~U32, cap, ops, hc0, q, hq, hc, hops)

def trace_new_string(+cap: U32, +ops: List<&2, E.Op<String>>, +hc0: {U32.is_eq(cap, 0) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hops: {TR.all_ok(String, q, ops) == True{} : Bool}) -> TR.TraceNew(~String, cap, ops):
  TR.trace_new(~String, cap, ops, hc0, q, hq, hc, hops)
