import Base
import ./proofs/lru.bend as LRUP
import ./src/lru.bend as LRU
import ./reference/lru/src/public.bend as LRUPub
import ./reference/lru/spec/clock.bend as LRUClock
import ./reference/lru/spec/cache.bend as LRUSpec
import ./reference/lru/proofs/public_trace.bend as LRUTrace
import ./proofs/lib/array.bend as AR
import ./proofs/lib/logic.bend as L
import ./spec/common.bend as SC
import ./src/dynamic_array.bend as DA
import ./spec/dynamic_array.bend as DAS
import ./types/dynamic_array.bend as DAT
import ./proofs/dynamic_array.bend as DAP
import ./proofs/dynamic_array/state.bend as DAST
import ./src/deque.bend as DQ
import ./spec/deque.bend as DQS
import ./types/deque.bend as DQT
import ./proofs/deque.bend as DQP
import ./proofs/deque/state.bend as DQSH
import ./proofs/deque/steps.bend as DQST
import ./proofs/deque/stepok.bend as DQK
import ./proofs/deque/trace.bend as DQTR
import ./src/queue.bend as QU
import ./spec/queue.bend as QUS
import ./types/queue.bend as QUT
import ./proofs/queue.bend as QUP
import ./proofs/queue/steps.bend as QUST
import ./proofs/queue/trace.bend as QUTR
import ./proofs/lib/order.bend as O
import ./src/binary_heap.bend as BH
import ./spec/binary_heap.bend as BHS
import ./types/binary_heap.bend as BHT
import ./proofs/binary_heap.bend as BHP
import ./proofs/binary_heap/state.bend as BHSH
import ./proofs/binary_heap/steps.bend as BHST
import ./proofs/binary_heap/trace.bend as BHTR
import ./src/bitset.bend as BI
import ./spec/common.bend as SCOM
import ./spec/bitset.bend as BIS
import ./types/bitset.bend as BIT
import ./proofs/bitset.bend as BIP
import ./proofs/bitset/state.bend as BIST
import ./proofs/bitset/steps.bend as BISP
import ./proofs/bitset/trace.bend as BITR
import ./src/balanced_search_tree.bend as BT
import ./spec/balanced_search_tree.bend as BTS
import ./types/balanced_search_tree.bend as BTT
import ./proofs/balanced_search_tree.bend as BTP
import ./proofs/balanced_search_tree/steps.bend as BTST
import ./proofs/balanced_search_tree/tree.bend as BTTR
import ./proofs/balanced_search_tree/trace.bend as BTTC
import ./src/lru/fast.bend as LRUF
import ./spec/lru_fast.bend as LRUFS
import ./types/lru_model.bend as LRUFT
import ./types/lru_fast.bend as LRUFE
import ./proofs/lru_fast.bend as LRUFP
import ./proofs/lru_fast/state.bend as LRUFSH
import ./proofs/lru_fast/steps.bend as LRUFSP
import ./proofs/lru_fast/trace.bend as LRUFTR

# Public correctness and trace laws, stated over the real src/ APIs and the
# independent spec/ models. Each law is discharged by its structure's proof
# entry module (proofs/<id>.bend). PROOF.bend imports this file.

# ============================ retained LRU ============================

law lru_entry_string_trace:
  for -V: Data
  for +zero_key: String
  for +zero_value: V
  for +capacity: U32
  for +size: U32
  for +requests: List<&2, LRUPub.Request<String, V>>
  for +events: List<&2, LRUClock.Event>
  LRUTrace.created_rel(V, zero_key, zero_value, requests, events, LRU.new_with_size(V, capacity, size), LRUSpec.new_with_size(String, V, capacity, size))
def lru_entry_string_trace(V, zero_key, zero_value, capacity, size, requests, events):
  LRUP.entry_string_trace(V, zero_key, zero_value, capacity, size, requests, events)

# ============================ Base.Array ==============================

law array_get_after_set_same:
  for -T: Data
  for +d: Nat
  for +t: AR.Tree<T>
  for +i: U32
  for +v: T
  for +x: T
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}
  for +hx: {SC.nth(T, AR.slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}
  for +pf: {AR.perfect(T, d, t) == True{} : Bool}
  {Array.get(T, Array.set(T, AR.thaw(T, t), i, v), i) == (AR.thaw(T, AR.upd(T, d, t, U32.to_nat(i), v)), v) : Array<T> & T}
def array_get_after_set_same(T, d, t, i, v, x, hd, hi, hx, pf):
  AR.get_set_same(T, d, t, i, v, x, hd, hi, hx, pf)

law array_get_after_set_other:
  for -T: Data
  for +d: Nat
  for +t: AR.Tree<T>
  for +i: U32
  for +j: U32
  for +v: T
  for +x: T
  for +y: T
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}
  for +hj: {Nat.is_lt(U32.to_nat(j), SC.pow2(d)) == True{} : Bool}
  for +ne: {Nat.is_eq(U32.to_nat(i), U32.to_nat(j)) == False{} : Bool}
  for +hx: {SC.nth(T, AR.slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}
  for +hy: {SC.nth(T, AR.slots(T, t), U32.to_nat(j)) == Some{y} : Maybe<&2, T>}
  for +pf: {AR.perfect(T, d, t) == True{} : Bool}
  {Array.get(T, Array.set(T, AR.thaw(T, t), i, v), j) == (AR.thaw(T, AR.upd(T, d, t, U32.to_nat(i), v)), y) : Array<T> & T}
def array_get_after_set_other(T, d, t, i, j, v, x, y, hd, hi, hj, ne, hx, hy, pf):
  AR.get_set_other(T, d, t, i, j, v, x, y, hd, hi, hj, ne, hx, hy, pf)

law array_new:
  for -T: Data
  for +d: Nat
  for +v: T
  {Array.new(T, d, v) == AR.thaw(T, AR.trep(T, d, v)) : Array<T>}
def array_new(T, d, v):
  AR.new(T, d, v)

# ============================ dynamic_array ===========================

law dynamic_array_new:
  for -T: Data
  {DAST.abs(T, DA.new(T)) == DAS.new(T) : DAS.Model<T>}
def dynamic_array_new(T):
  DAP.new_abs(T)

law dynamic_array_new_invariant:
  for -T: Data
  DAST.Inv(T, DA.new(T))
def dynamic_array_new_invariant(T):
  DAP.new_inv(T)

law dynamic_array_with_limit:
  for -T: Data
  for +k: Nat
  {DAST.abs(T, DA.with_limit(T, k)) == DAS.with_limit(T, k) : DAS.Model<T>}
def dynamic_array_with_limit(T, k):
  DAP.with_limit_abs(T, k)

law dynamic_array_step:
  for -T: Data
  for +sh: DAST.Shadow<T>
  for +op: DAT.Op<T>
  for +g: {DAST.good(T, sh) == True{} : Bool}
  {DAP.view1(T, DA.step(T, DAST.real(T, sh), op)) == DAS.step(T, DAST.abs(T, DAST.real(T, sh)), op) : DAS.Model<T> & DAT.Obs<T>}
def dynamic_array_step(T, sh, op, g):
  DAP.step_refines(T, sh, op, g)

law dynamic_array_step_invariant:
  for -T: Data
  for +sh: DAST.Shadow<T>
  for +op: DAT.Op<T>
  for +g: {DAST.good(T, sh) == True{} : Bool}
  DAST.Inv(T, Pair.fst(DA.DynArray<T>, DAT.Obs<T>, DA.step(T, DAST.real(T, sh), op)))
def dynamic_array_step_invariant(T, sh, op, g):
  DAP.step_preserves(T, sh, op, g)

law dynamic_array_trace:
  for -T: Data
  for +ops: List<&2, DAT.Op<T>>
  {DAP.view(T, DA.run(T, ops, DA.new(T))) == DAS.run(T, ops, DAS.new(T)) : DAS.Model<T> & List<&2, DAT.Obs<T>>}
def dynamic_array_trace(T, ops):
  DAP.trace_new(T, ops)

law dynamic_array_trace_invariant:
  for -T: Data
  for +ops: List<&2, DAT.Op<T>>
  DAST.Inv(T, Pair.fst(DA.DynArray<T>, List<&2, DAT.Obs<T>>, DA.run(T, ops, DA.new(T))))
def dynamic_array_trace_invariant(T, ops):
  DAP.trace_new_inv(T, ops)

law dynamic_array_trace_limited:
  for -T: Data
  for +k: Nat
  for +ops: List<&2, DAT.Op<T>>
  {DAP.view(T, DA.run(T, ops, DA.with_limit(T, k))) == DAS.run(T, ops, DAS.with_limit(T, k)) : DAS.Model<T> & List<&2, DAT.Obs<T>>}
def dynamic_array_trace_limited(T, k, ops):
  DAP.trace_with_limit(T, k, ops)

law dynamic_array_trace_limited_invariant:
  for -T: Data
  for +k: Nat
  for +ops: List<&2, DAT.Op<T>>
  DAST.Inv(T, Pair.fst(DA.DynArray<T>, List<&2, DAT.Obs<T>>, DA.run(T, ops, DA.with_limit(T, k))))
def dynamic_array_trace_limited_invariant(T, k, ops):
  DAP.trace_with_limit_inv(T, k, ops)


# ---- executable specializations (closed element type; see src/dynamic_array.bend) ----
# The `*_at` definitions are the ones tests and benchmarks actually run. They
# are proved equal to the parametric definitions above, so these laws are the
# same statements at the element types the project instantiates.

law dynamic_array_new_at_u32:
  {DAST.abs(U32, DA.new_at(~U32)) == DAS.new(U32) : DAS.Model<U32>}
def dynamic_array_new_at_u32():
  DAP.new_at_abs(~U32)

law dynamic_array_new_at_invariant_u32:
  DAST.Inv(U32, DA.new_at(~U32))
def dynamic_array_new_at_invariant_u32():
  DAP.new_at_inv(~U32)

law dynamic_array_with_limit_at_u32:
  for +k: Nat
  {DAST.abs(U32, DA.with_limit_at(~U32, k)) == DAS.with_limit(U32, k) : DAS.Model<U32>}
def dynamic_array_with_limit_at_u32(k):
  DAP.with_limit_at_abs(~U32, k)

law dynamic_array_step_at_u32:
  for +sh: DAST.Shadow<U32>
  for +op: DAT.Op<U32>
  for +g: {DAST.good(U32, sh) == True{} : Bool}
  {DAP.view1(U32, DA.step_at(~U32, DAST.real(U32, sh), op)) == DAS.step(U32, DAST.abs(U32, DAST.real(U32, sh)), op) : DAS.Model<U32> & DAT.Obs<U32>}
def dynamic_array_step_at_u32(sh, op, g):
  DAP.step_at_refines(~U32, sh, op, g)

law dynamic_array_step_at_invariant_u32:
  for +sh: DAST.Shadow<U32>
  for +op: DAT.Op<U32>
  for +g: {DAST.good(U32, sh) == True{} : Bool}
  DAST.Inv(U32, Pair.fst(DA.DynArray<U32>, DAT.Obs<U32>, DA.step_at(~U32, DAST.real(U32, sh), op)))
def dynamic_array_step_at_invariant_u32(sh, op, g):
  DAP.step_at_preserves(~U32, sh, op, g)

law dynamic_array_trace_at_u32:
  for +ops: List<&2, DAT.Op<U32>>
  {DAP.view(U32, DA.run_at(~U32, ops, DA.new_at(~U32))) == DAS.run(U32, ops, DAS.new(U32)) : DAS.Model<U32> & List<&2, DAT.Obs<U32>>}
def dynamic_array_trace_at_u32(ops):
  DAP.trace_new_at(~U32, ops)

law dynamic_array_trace_at_invariant_u32:
  for +ops: List<&2, DAT.Op<U32>>
  DAST.Inv(U32, Pair.fst(DA.DynArray<U32>, List<&2, DAT.Obs<U32>>, DA.run_at(~U32, ops, DA.new_at(~U32))))
def dynamic_array_trace_at_invariant_u32(ops):
  DAP.trace_new_at_inv(~U32, ops)

law dynamic_array_trace_limited_at_u32:
  for +k: Nat
  for +ops: List<&2, DAT.Op<U32>>
  {DAP.view(U32, DA.run_at(~U32, ops, DA.with_limit_at(~U32, k))) == DAS.run(U32, ops, DAS.with_limit(U32, k)) : DAS.Model<U32> & List<&2, DAT.Obs<U32>>}
def dynamic_array_trace_limited_at_u32(k, ops):
  DAP.trace_with_limit_at(~U32, k, ops)

law dynamic_array_trace_limited_at_invariant_u32:
  for +k: Nat
  for +ops: List<&2, DAT.Op<U32>>
  DAST.Inv(U32, Pair.fst(DA.DynArray<U32>, List<&2, DAT.Obs<U32>>, DA.run_at(~U32, ops, DA.with_limit_at(~U32, k))))
def dynamic_array_trace_limited_at_invariant_u32(k, ops):
  DAP.trace_with_limit_at_inv(~U32, k, ops)

law dynamic_array_new_at_nat:
  {DAST.abs(Nat, DA.new_at(~Nat)) == DAS.new(Nat) : DAS.Model<Nat>}
def dynamic_array_new_at_nat():
  DAP.new_at_abs(~Nat)

law dynamic_array_new_at_invariant_nat:
  DAST.Inv(Nat, DA.new_at(~Nat))
def dynamic_array_new_at_invariant_nat():
  DAP.new_at_inv(~Nat)

law dynamic_array_with_limit_at_nat:
  for +k: Nat
  {DAST.abs(Nat, DA.with_limit_at(~Nat, k)) == DAS.with_limit(Nat, k) : DAS.Model<Nat>}
def dynamic_array_with_limit_at_nat(k):
  DAP.with_limit_at_abs(~Nat, k)

law dynamic_array_step_at_nat:
  for +sh: DAST.Shadow<Nat>
  for +op: DAT.Op<Nat>
  for +g: {DAST.good(Nat, sh) == True{} : Bool}
  {DAP.view1(Nat, DA.step_at(~Nat, DAST.real(Nat, sh), op)) == DAS.step(Nat, DAST.abs(Nat, DAST.real(Nat, sh)), op) : DAS.Model<Nat> & DAT.Obs<Nat>}
def dynamic_array_step_at_nat(sh, op, g):
  DAP.step_at_refines(~Nat, sh, op, g)

law dynamic_array_step_at_invariant_nat:
  for +sh: DAST.Shadow<Nat>
  for +op: DAT.Op<Nat>
  for +g: {DAST.good(Nat, sh) == True{} : Bool}
  DAST.Inv(Nat, Pair.fst(DA.DynArray<Nat>, DAT.Obs<Nat>, DA.step_at(~Nat, DAST.real(Nat, sh), op)))
def dynamic_array_step_at_invariant_nat(sh, op, g):
  DAP.step_at_preserves(~Nat, sh, op, g)

law dynamic_array_trace_at_nat:
  for +ops: List<&2, DAT.Op<Nat>>
  {DAP.view(Nat, DA.run_at(~Nat, ops, DA.new_at(~Nat))) == DAS.run(Nat, ops, DAS.new(Nat)) : DAS.Model<Nat> & List<&2, DAT.Obs<Nat>>}
def dynamic_array_trace_at_nat(ops):
  DAP.trace_new_at(~Nat, ops)

law dynamic_array_trace_at_invariant_nat:
  for +ops: List<&2, DAT.Op<Nat>>
  DAST.Inv(Nat, Pair.fst(DA.DynArray<Nat>, List<&2, DAT.Obs<Nat>>, DA.run_at(~Nat, ops, DA.new_at(~Nat))))
def dynamic_array_trace_at_invariant_nat(ops):
  DAP.trace_new_at_inv(~Nat, ops)

law dynamic_array_trace_limited_at_nat:
  for +k: Nat
  for +ops: List<&2, DAT.Op<Nat>>
  {DAP.view(Nat, DA.run_at(~Nat, ops, DA.with_limit_at(~Nat, k))) == DAS.run(Nat, ops, DAS.with_limit(Nat, k)) : DAS.Model<Nat> & List<&2, DAT.Obs<Nat>>}
def dynamic_array_trace_limited_at_nat(k, ops):
  DAP.trace_with_limit_at(~Nat, k, ops)

law dynamic_array_trace_limited_at_invariant_nat:
  for +k: Nat
  for +ops: List<&2, DAT.Op<Nat>>
  DAST.Inv(Nat, Pair.fst(DA.DynArray<Nat>, List<&2, DAT.Obs<Nat>>, DA.run_at(~Nat, ops, DA.with_limit_at(~Nat, k))))
def dynamic_array_trace_limited_at_invariant_nat(k, ops):
  DAP.trace_with_limit_at_inv(~Nat, k, ops)

law dynamic_array_new_at_string:
  {DAST.abs(String, DA.new_at(~String)) == DAS.new(String) : DAS.Model<String>}
def dynamic_array_new_at_string():
  DAP.new_at_abs(~String)

law dynamic_array_new_at_invariant_string:
  DAST.Inv(String, DA.new_at(~String))
def dynamic_array_new_at_invariant_string():
  DAP.new_at_inv(~String)

law dynamic_array_with_limit_at_string:
  for +k: Nat
  {DAST.abs(String, DA.with_limit_at(~String, k)) == DAS.with_limit(String, k) : DAS.Model<String>}
def dynamic_array_with_limit_at_string(k):
  DAP.with_limit_at_abs(~String, k)

law dynamic_array_step_at_string:
  for +sh: DAST.Shadow<String>
  for +op: DAT.Op<String>
  for +g: {DAST.good(String, sh) == True{} : Bool}
  {DAP.view1(String, DA.step_at(~String, DAST.real(String, sh), op)) == DAS.step(String, DAST.abs(String, DAST.real(String, sh)), op) : DAS.Model<String> & DAT.Obs<String>}
def dynamic_array_step_at_string(sh, op, g):
  DAP.step_at_refines(~String, sh, op, g)

law dynamic_array_step_at_invariant_string:
  for +sh: DAST.Shadow<String>
  for +op: DAT.Op<String>
  for +g: {DAST.good(String, sh) == True{} : Bool}
  DAST.Inv(String, Pair.fst(DA.DynArray<String>, DAT.Obs<String>, DA.step_at(~String, DAST.real(String, sh), op)))
def dynamic_array_step_at_invariant_string(sh, op, g):
  DAP.step_at_preserves(~String, sh, op, g)

law dynamic_array_trace_at_string:
  for +ops: List<&2, DAT.Op<String>>
  {DAP.view(String, DA.run_at(~String, ops, DA.new_at(~String))) == DAS.run(String, ops, DAS.new(String)) : DAS.Model<String> & List<&2, DAT.Obs<String>>}
def dynamic_array_trace_at_string(ops):
  DAP.trace_new_at(~String, ops)

law dynamic_array_trace_at_invariant_string:
  for +ops: List<&2, DAT.Op<String>>
  DAST.Inv(String, Pair.fst(DA.DynArray<String>, List<&2, DAT.Obs<String>>, DA.run_at(~String, ops, DA.new_at(~String))))
def dynamic_array_trace_at_invariant_string(ops):
  DAP.trace_new_at_inv(~String, ops)

law dynamic_array_trace_limited_at_string:
  for +k: Nat
  for +ops: List<&2, DAT.Op<String>>
  {DAP.view(String, DA.run_at(~String, ops, DA.with_limit_at(~String, k))) == DAS.run(String, ops, DAS.with_limit(String, k)) : DAS.Model<String> & List<&2, DAT.Obs<String>>}
def dynamic_array_trace_limited_at_string(k, ops):
  DAP.trace_with_limit_at(~String, k, ops)

law dynamic_array_trace_limited_at_invariant_string:
  for +k: Nat
  for +ops: List<&2, DAT.Op<String>>
  DAST.Inv(String, Pair.fst(DA.DynArray<String>, List<&2, DAT.Obs<String>>, DA.run_at(~String, ops, DA.with_limit_at(~String, k))))
def dynamic_array_trace_limited_at_invariant_string(k, ops):
  DAP.trace_with_limit_at_inv(~String, k, ops)

# ============================== deque =================================
# The ring buffer (src/deque.bend). Base.Array is linear, so the laws are
# about the deque BUILT from a Data shadow (DQSH.real). The only premise is
# the representation's capacity condition, on the PEAK size: a push onto a
# deque holding fewer than 2^q elements, q <= 31 (DQST.pushok); for traces,
# DQTR.fits (every push happens below 2^q elements). It bounds neither the
# length of a trace nor the number of pushes. Every law is a template in the
# element type, restated at both checked instances (U32, String).

law deque_u32_new:
  {DQSH.model(U32, DQSH.initial(U32)) == Nil{} : List<&2, U32>}
def deque_u32_new():
  DQP.new_abs(~U32)

law deque_u32_new_invariant:
  {DQSH.good(U32, DQSH.initial(U32)) == True{} : Bool}
def deque_u32_new_invariant():
  DQP.new_inv(~U32)

law deque_u32_new_is_the_constructor:
  {DQ.new(~U32) == DQSH.real(U32, DQSH.initial(U32)) : DQ.Deque<U32>}
def deque_u32_new_is_the_constructor():
  DQP.new_real(~U32)

law deque_u32_step:
  for +sh: DQSH.Shadow<U32>
  for op: DQT.Op<U32>
  for +g: {DQSH.good(U32, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hp: {DQST.pushok(U32, q, op, DQSH.model(U32, sh)) == True{} : Bool}
  DQK.StepOK(~U32, sh, op)
def deque_u32_step(sh, op, g, q, hq, hp):
  DQP.step_ok(~U32, sh, op, g, q, hq, hp)

law deque_u32_shadow_unique:
  for +a: DQSH.Shadow<U32>
  for +b: DQSH.Shadow<U32>
  for +e: {DQSH.real(U32, a) == DQSH.real(U32, b) : DQ.Deque<U32>}
  {a == b : DQSH.Shadow<U32>}
def deque_u32_shadow_unique(a, b, e):
  DQP.shadow_unique(~U32, a, b, e)

law deque_u32_trace:
  for +ops: List<&2, DQT.Op<U32>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hf: {DQTR.fits(U32, q, ops, Nil{}) == True{} : Bool}
  DQTR.TraceOK(~U32, ops, DQSH.initial(U32))
def deque_u32_trace(ops, q, hq, hf):
  DQP.trace_new(~U32, ops, q, hq, hf)

law deque_string_new:
  {DQSH.model(String, DQSH.initial(String)) == Nil{} : List<&2, String>}
def deque_string_new():
  DQP.new_abs(~String)

law deque_string_new_invariant:
  {DQSH.good(String, DQSH.initial(String)) == True{} : Bool}
def deque_string_new_invariant():
  DQP.new_inv(~String)

law deque_string_new_is_the_constructor:
  {DQ.new(~String) == DQSH.real(String, DQSH.initial(String)) : DQ.Deque<String>}
def deque_string_new_is_the_constructor():
  DQP.new_real(~String)

law deque_string_step:
  for +sh: DQSH.Shadow<String>
  for op: DQT.Op<String>
  for +g: {DQSH.good(String, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hp: {DQST.pushok(String, q, op, DQSH.model(String, sh)) == True{} : Bool}
  DQK.StepOK(~String, sh, op)
def deque_string_step(sh, op, g, q, hq, hp):
  DQP.step_ok(~String, sh, op, g, q, hq, hp)

law deque_string_shadow_unique:
  for +a: DQSH.Shadow<String>
  for +b: DQSH.Shadow<String>
  for +e: {DQSH.real(String, a) == DQSH.real(String, b) : DQ.Deque<String>}
  {a == b : DQSH.Shadow<String>}
def deque_string_shadow_unique(a, b, e):
  DQP.shadow_unique(~String, a, b, e)

law deque_string_trace:
  for +ops: List<&2, DQT.Op<String>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hf: {DQTR.fits(String, q, ops, Nil{}) == True{} : Bool}
  DQTR.TraceOK(~String, ops, DQSH.initial(String))
def deque_string_trace(ops, q, hq, hf):
  DQP.trace_new(~String, ops, q, hq, hf)

# ============================== queue =================================
# The FIFO specialization of the ring deque (enqueue = push_back, dequeue =
# pop_front, peek = peek_front); same shadow, same capacity condition.

law queue_u32_new:
  {DQSH.model(U32, DQSH.initial(U32)) == Nil{} : List<&2, U32>}
def queue_u32_new():
  QUP.new_abs(~U32)

law queue_u32_new_invariant:
  {DQSH.good(U32, DQSH.initial(U32)) == True{} : Bool}
def queue_u32_new_invariant():
  QUP.new_inv(~U32)

law queue_u32_new_is_the_constructor:
  {QU.new(~U32) == QUST.real(~U32, DQSH.initial(U32)) : QU.Queue<U32>}
def queue_u32_new_is_the_constructor():
  QUP.new_real(~U32)

law queue_u32_step:
  for +sh: DQSH.Shadow<U32>
  for +op: QUT.Op<U32>
  for +g: {DQSH.good(U32, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hp: {DQST.pushok(U32, q, QUST.dop(U32, op), DQSH.model(U32, sh)) == True{} : Bool}
  QUST.StepOK(~U32, sh, op)
def queue_u32_step(sh, op, g, q, hq, hp):
  QUP.step_ok(~U32, sh, op, g, q, hq, hp)

law queue_u32_trace:
  for +ops: List<&2, QUT.Op<U32>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hf: {QUTR.fits(U32, q, ops, Nil{}) == True{} : Bool}
  QUTR.TraceOK(~U32, ops, DQSH.initial(U32))
def queue_u32_trace(ops, q, hq, hf):
  QUP.trace_new(~U32, ops, q, hq, hf)

law queue_string_new:
  {DQSH.model(String, DQSH.initial(String)) == Nil{} : List<&2, String>}
def queue_string_new():
  QUP.new_abs(~String)

law queue_string_new_invariant:
  {DQSH.good(String, DQSH.initial(String)) == True{} : Bool}
def queue_string_new_invariant():
  QUP.new_inv(~String)

law queue_string_new_is_the_constructor:
  {QU.new(~String) == QUST.real(~String, DQSH.initial(String)) : QU.Queue<String>}
def queue_string_new_is_the_constructor():
  QUP.new_real(~String)

law queue_string_step:
  for +sh: DQSH.Shadow<String>
  for +op: QUT.Op<String>
  for +g: {DQSH.good(String, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hp: {DQST.pushok(String, q, QUST.dop(String, op), DQSH.model(String, sh)) == True{} : Bool}
  QUST.StepOK(~String, sh, op)
def queue_string_step(sh, op, g, q, hq, hp):
  QUP.step_ok(~String, sh, op, g, q, hq, hp)

law queue_string_trace:
  for +ops: List<&2, QUT.Op<String>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hf: {QUTR.fits(String, q, ops, Nil{}) == True{} : Bool}
  QUTR.TraceOK(~String, ops, DQSH.initial(String))
def queue_string_trace(ops, q, hq, hf):
  QUP.trace_new(~String, ops, q, hq, hf)

# =========================== binary_heap ==============================
# The block is a linear Base.Array, so -- as for dynamic_array, bitset and
# deque -- the laws are about the heap BUILT from a Data mirror tree
# (BHSH.real of a shadow). Generic over a comparator; restated at both
# checked instances. `room` is the representation's capacity condition: the
# size plus the elements still to be added stays below 2^q, q <= 31 (Base
# arrays have at most 2^31 slots); it does not bound the trace length.

law binary_heap_u32_new:
  {BHSH.model(~U32, ~U32.cmp, BHSH.initial(~U32)) == Nil{} : List<&2, U32>}
def binary_heap_u32_new():
  BHP.new_abs(~U32, ~U32.cmp)

law binary_heap_u32_new_good:
  {BHSH.good(~U32, ~U32.cmp, BHSH.initial(~U32)) == True{} : Bool}
def binary_heap_u32_new_good():
  BHP.new_inv(~U32, ~U32.cmp)

law binary_heap_u32_new_is_the_constructor:
  {BH.new(~U32) == BHSH.real(~U32, BHSH.initial(~U32)) : BH.Heap<U32>}
def binary_heap_u32_new_is_the_constructor():
  BHP.new_real(~U32, ~U32.cmp)

law binary_heap_u32_abstraction_of_a_real_heap:
  for +sh: BHSH.Shadow<U32>
  {BHSH.abs(~U32, ~U32.cmp, BHSH.real(~U32, sh)) == BHSH.model(~U32, ~U32.cmp, sh) : List<&2, U32>}
def binary_heap_u32_abstraction_of_a_real_heap(sh):
  BHP.abs_real(~U32, ~U32.cmp, sh)

law binary_heap_string_new:
  {BHSH.model(~String, ~String.order, BHSH.initial(~String)) == Nil{} : List<&2, String>}
def binary_heap_string_new():
  BHP.new_abs(~String, ~String.order)

law binary_heap_string_new_is_the_constructor:
  {BH.new(~String) == BHSH.real(~String, BHSH.initial(~String)) : BH.Heap<String>}
def binary_heap_string_new_is_the_constructor():
  BHP.new_real(~String, ~String.order)

law binary_heap_string_abstraction_of_a_real_heap:
  for +sh: BHSH.Shadow<String>
  {BHSH.abs(~String, ~String.order, BHSH.real(~String, sh)) == BHSH.model(~String, ~String.order, sh) : List<&2, String>}
def binary_heap_string_abstraction_of_a_real_heap(sh):
  BHP.abs_real(~String, ~String.order, sh)

law binary_heap_u32_step:
  for sh: BHSH.Shadow<U32>
  for op: BHT.Op<U32>
  for +g: {BHSH.good(~U32, ~U32.cmp, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +room: {Nat.is_lt(Nat.add(BHSH.sh_size(~U32, sh), BHST.pushcost(~U32, op)), SCOM.pow2(q)) == True{} : Bool}
  BHST.StepOK(~U32, ~U32.cmp, sh, op)
def binary_heap_u32_step(sh, op, g, q, hq, room):
  BHP.u32_step_ok(sh, op, g, q, hq, room)

law binary_heap_u32_trace:
  for +ops: List<&2, BHT.Op<U32>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +room: {Nat.is_lt(BHTR.pushes(~U32, ops), SCOM.pow2(q)) == True{} : Bool}
  BHTR.TraceOK(~U32, ~U32.cmp, ops, BHSH.initial(~U32))
def binary_heap_u32_trace(ops, q, hq, room):
  BHP.u32_trace(ops, q, hq, room)

law binary_heap_u32_new_invariant:
  BHSH.Inv(~U32, ~U32.cmp, BH.new(~U32))
def binary_heap_u32_new_invariant():
  BHP.u32_new_inv()

law binary_heap_string_step:
  for sh: BHSH.Shadow<String>
  for op: BHT.Op<String>
  for +g: {BHSH.good(~String, ~String.order, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +room: {Nat.is_lt(Nat.add(BHSH.sh_size(~String, sh), BHST.pushcost(~String, op)), SCOM.pow2(q)) == True{} : Bool}
  BHST.StepOK(~String, ~String.order, sh, op)
def binary_heap_string_step(sh, op, g, q, hq, room):
  BHP.string_step_ok(sh, op, g, q, hq, room)

law binary_heap_string_trace:
  for +ops: List<&2, BHT.Op<String>>
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +room: {Nat.is_lt(BHTR.pushes(~String, ops), SCOM.pow2(q)) == True{} : Bool}
  BHTR.TraceOK(~String, ~String.order, ops, BHSH.initial(~String))
def binary_heap_string_trace(ops, q, hq, room):
  BHP.string_trace(ops, q, hq, room)

law binary_heap_string_new_invariant:
  BHSH.Inv(~String, ~String.order, BH.new(~String))
def binary_heap_string_new_invariant():
  BHP.string_new_inv()

# ============================== bitset ================================

law bitset_new:
  for +n: Nat
  for +h: {Nat.is_le(n, Nat.mul(SCOM.pow2(BI.depth_for(n)), 32n)) == True{} : Bool}
  {BIST.model(BITR.initial(n)) == BIS.new(n) : List<&2, Bool>}
def bitset_new(n, h):
  BIP.new_abs(n, h)

law bitset_new_invariant:
  for +n: Nat
  for +h: {Nat.is_le(n, Nat.mul(SCOM.pow2(BI.depth_for(n)), 32n)) == True{} : Bool}
  {BIST.good(BITR.initial(n)) == True{} : Bool}
def bitset_new_invariant(n, h):
  BIP.new_inv(n, h)

law bitset_new_is_the_constructor:
  for +n: Nat
  {BI.new(n) == BIST.real(BITR.initial(n)) : BI.Bitset}
def bitset_new_is_the_constructor(n):
  BIP.new_real(n)

law bitset_from_bools:
  for +ys: List<&2, Bool>
  for +hf: {Nat.is_le(BI.bool_count(ys), Nat.mul(SCOM.pow2(BI.depth_for(BI.bool_count(ys))), 32n)) == True{} : Bool}
  BISP.FromOK(ys)
def bitset_from_bools(ys, hf):
  BIP.from_bools(ys, hf)

law bitset_step:
  for sh: BIST.Sh
  for op: BIT.Op
  for +g: {BIST.good(sh) == True{} : Bool}
  BISP.StepOK(sh, op)
def bitset_step(sh, op, g):
  BIP.step_ok(sh, op, g)

law bitset_shadow_unique:
  for +a: BIST.Sh
  for +b: BIST.Sh
  for +e: {BIST.real(a) == BIST.real(b) : BI.Bitset}
  {a == b : BIST.Sh}
def bitset_shadow_unique(a, b, e):
  BIP.shadow_unique(a, b, e)

law bitset_trace:
  for +n: Nat
  for +ops: List<&2, BIT.Op>
  for +h: {Nat.is_le(n, Nat.mul(SCOM.pow2(BI.depth_for(n)), 32n)) == True{} : Bool}
  BITR.TraceOK(ops, BITR.initial(n))
def bitset_trace(n, ops, h):
  BIP.trace_new(n, ops, h)

# ======================== balanced_search_tree ========================
# Red-black binary tree ordered map (src/balanced_search_tree.bend). The
# proofs are templates over a comparator with total-order laws; the laws are
# stated at the two instances src/ exposes: (U32, U32.cmp) and
# (String, String.order). Values are an erased type. The invariant
# (strictly increasing keys, red-black balance, cached size) is kept by
# every operation, and balance is also restated in textbook form.

law balanced_search_tree_new_balanced:
  for -K: Data
  for -V: Data
  {BTTR.bal(K, V, BT.Leaf{}) == True{} : Bool}
def balanced_search_tree_new_balanced(K, V):
  BTP.new_balanced(K, V)

law balanced_search_tree_leaf_black:
  for -K: Data
  for -V: Data
  {BT.is_red(K, V, BT.Leaf{}) == False{} : Bool}
def balanced_search_tree_leaf_black(K, V):
  BTP.leaf_black(K, V)

law balanced_search_tree_u32_new:
  for -V: Data
  {BTST.abs(~U32, ~U32.cmp, V, BT.new(U32, V)) == Nil{} : List<&2, BTT.Entry<U32, V>>}
def balanced_search_tree_u32_new(V):
  BTP.new_abs(~U32, ~U32.cmp, V)

law balanced_search_tree_u32_new_invariant:
  for -V: Data
  {BTST.inv(~U32, ~U32.cmp, V, BT.new(U32, V)) == True{} : Bool}
def balanced_search_tree_u32_new_invariant(V):
  BTP.new_inv(~U32, ~U32.cmp, V)

law balanced_search_tree_u32_step:
  for -V: Data
  for +s: BT.OrdMap<U32, V>
  for +op: BTT.Op<U32, V>
  for +g: {BTST.inv(~U32, ~U32.cmp, V, s) == True{} : Bool}
  BTST.StepOK(~U32, ~U32.cmp, V, s, op)
def balanced_search_tree_u32_step(V, s, op, g):
  BTP.u32_step_ok(V, s, op, g)

law balanced_search_tree_u32_trace:
  for -V: Data
  for +ops: List<&2, BTT.Op<U32, V>>
  {BTTC.view(~U32, ~U32.cmp, ~O.u32_order, V, BT.run_u32(V, ops, BT.new(U32, V))) == BTS.run(~U32, ~U32.cmp, V, ops, Nil{}) : List<&2, BTT.Entry<U32, V>> & List<&2, BTT.Obs<U32, V>>}
def balanced_search_tree_u32_trace(V, ops):
  BTP.u32_trace(V, ops)

law balanced_search_tree_u32_trace_invariant:
  for -V: Data
  for +ops: List<&2, BTT.Op<U32, V>>
  {BTST.inv(~U32, ~U32.cmp, V, Pair.fst(BT.OrdMap<U32, V>, List<&2, BTT.Obs<U32, V>>, BT.run_u32(V, ops, BT.new(U32, V)))) == True{} : Bool}
def balanced_search_tree_u32_trace_invariant(V, ops):
  BTP.u32_trace_inv(V, ops)

law balanced_search_tree_u32_insert_balanced:
  for -V: Data
  for +t: BT.Tree<U32, V>
  for +k: U32
  for +v: V
  for +b: {BTTR.bal(U32, V, t) == True{} : Bool}
  {BTTR.bal(U32, V, BT.insert_tree(~U32, ~U32.cmp, V, t, k, v)) == True{} : Bool}
def balanced_search_tree_u32_insert_balanced(V, t, k, v, b):
  BTP.u32_insert_balanced(V, t, k, v, b)

law balanced_search_tree_u32_remove_balanced:
  for -V: Data
  for +t: BT.Tree<U32, V>
  for +k: U32
  for +b: {BTTR.bal(U32, V, t) == True{} : Bool}
  {BTTR.bal(U32, V, BT.remove_tree(~U32, ~U32.cmp, V, t, k)) == True{} : Bool}
def balanced_search_tree_u32_remove_balanced(V, t, k, b):
  BTP.u32_remove_balanced(V, t, k, b)

law balanced_search_tree_u32_root_black:
  for -V: Data
  for +t: BT.Tree<U32, V>
  for +b: {BTTR.bal(U32, V, t) == True{} : Bool}
  {BT.is_red(U32, V, t) == False{} : Bool}
def balanced_search_tree_u32_root_black(V, t, b):
  BTP.u32_root_black(V, t, b)

law balanced_search_tree_u32_no_red_red:
  for -V: Data
  for +t: BT.Tree<U32, V>
  for +b: {BTTR.bal(U32, V, t) == True{} : Bool}
  {BTTR.nrr_all(U32, V, t) == True{} : Bool}
def balanced_search_tree_u32_no_red_red(V, t, b):
  BTP.u32_no_red_red(V, t, b)

law balanced_search_tree_u32_uniform_black_height:
  for -V: Data
  for +t: BT.Tree<U32, V>
  for +b: {BTTR.bal(U32, V, t) == True{} : Bool}
  {BTTR.all_eq(BTTR.bh(U32, V, t), BTTR.paths(U32, V, t)) == True{} : Bool}
def balanced_search_tree_u32_uniform_black_height(V, t, b):
  BTP.u32_uniform_black_height(V, t, b)

law balanced_search_tree_string_new:
  for -V: Data
  {BTST.abs(~String, ~String.order, V, BT.new(String, V)) == Nil{} : List<&2, BTT.Entry<String, V>>}
def balanced_search_tree_string_new(V):
  BTP.new_abs(~String, ~String.order, V)

law balanced_search_tree_string_new_invariant:
  for -V: Data
  {BTST.inv(~String, ~String.order, V, BT.new(String, V)) == True{} : Bool}
def balanced_search_tree_string_new_invariant(V):
  BTP.new_inv(~String, ~String.order, V)

law balanced_search_tree_string_step:
  for -V: Data
  for +s: BT.OrdMap<String, V>
  for +op: BTT.Op<String, V>
  for +g: {BTST.inv(~String, ~String.order, V, s) == True{} : Bool}
  BTST.StepOK(~String, ~String.order, V, s, op)
def balanced_search_tree_string_step(V, s, op, g):
  BTP.string_step_ok(V, s, op, g)

law balanced_search_tree_string_trace:
  for -V: Data
  for +ops: List<&2, BTT.Op<String, V>>
  {BTTC.view(~String, ~String.order, ~O.string_order, V, BT.run_string(V, ops, BT.new(String, V))) == BTS.run(~String, ~String.order, V, ops, Nil{}) : List<&2, BTT.Entry<String, V>> & List<&2, BTT.Obs<String, V>>}
def balanced_search_tree_string_trace(V, ops):
  BTP.string_trace(V, ops)

law balanced_search_tree_string_trace_invariant:
  for -V: Data
  for +ops: List<&2, BTT.Op<String, V>>
  {BTST.inv(~String, ~String.order, V, Pair.fst(BT.OrdMap<String, V>, List<&2, BTT.Obs<String, V>>, BT.run_string(V, ops, BT.new(String, V)))) == True{} : Bool}
def balanced_search_tree_string_trace_invariant(V, ops):
  BTP.string_trace_inv(V, ops)

law balanced_search_tree_string_insert_balanced:
  for -V: Data
  for +t: BT.Tree<String, V>
  for +k: String
  for +v: V
  for +b: {BTTR.bal(String, V, t) == True{} : Bool}
  {BTTR.bal(String, V, BT.insert_tree(~String, ~String.order, V, t, k, v)) == True{} : Bool}
def balanced_search_tree_string_insert_balanced(V, t, k, v, b):
  BTP.string_insert_balanced(V, t, k, v, b)

law balanced_search_tree_string_remove_balanced:
  for -V: Data
  for +t: BT.Tree<String, V>
  for +k: String
  for +b: {BTTR.bal(String, V, t) == True{} : Bool}
  {BTTR.bal(String, V, BT.remove_tree(~String, ~String.order, V, t, k)) == True{} : Bool}
def balanced_search_tree_string_remove_balanced(V, t, k, b):
  BTP.string_remove_balanced(V, t, k, b)

law balanced_search_tree_string_root_black:
  for -V: Data
  for +t: BT.Tree<String, V>
  for +b: {BTTR.bal(String, V, t) == True{} : Bool}
  {BT.is_red(String, V, t) == False{} : Bool}
def balanced_search_tree_string_root_black(V, t, b):
  BTP.string_root_black(V, t, b)

law balanced_search_tree_string_no_red_red:
  for -V: Data
  for +t: BT.Tree<String, V>
  for +b: {BTTR.bal(String, V, t) == True{} : Bool}
  {BTTR.nrr_all(String, V, t) == True{} : Bool}
def balanced_search_tree_string_no_red_red(V, t, b):
  BTP.string_no_red_red(V, t, b)

law balanced_search_tree_string_uniform_black_height:
  for -V: Data
  for +t: BT.Tree<String, V>
  for +b: {BTTR.bal(String, V, t) == True{} : Bool}
  {BTTR.all_eq(BTTR.bh(String, V, t), BTTR.paths(String, V, t)) == True{} : Bool}
def balanced_search_tree_string_uniform_black_height(V, t, b):
  BTP.string_uniform_black_height(V, t, b)

# ============================ indexed LRU =============================
# src/lru/fast.bend (the runtime the benchmarks measure): a crit-bit key table
# over slot arenas with an intrusive recency chain, a free list and limb
# counters. As for the other array-backed structures the laws are about the
# cache BUILT from a Data mirror (LRUFSH.real of a shadow), against the
# independent list model spec/lru_fast.bend (entries in recency order with
# deadlines; expiry by the retained numeric semantics). Values are an erased
# type parameter; the laws are stated at V = U32 and V = String. `hc` / `hops`
# are the capacity condition: every capacity the cache takes (initial and
# Resize) is within 2^q, q <= 31 (slots are Base array indices).

law lru_fast_u32_new_is_the_constructor:
  for +cap: U32
  {LRUF.init(~U32, cap) == LRUFSH.real(~U32, LRUFSH.initial(~U32, cap)) : LRUF.Fast<U32>}
def lru_fast_u32_new_is_the_constructor(cap):
  LRUFP.new_real(~U32, cap)

law lru_fast_u32_new_accepts:
  for +cap: U32
  for +h0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}
  {LRUF.new(~U32, cap) == LRUF.Made{LRUF.init(~U32, cap)} : LRUF.Made<U32>}
def lru_fast_u32_new_accepts(cap, h0, h1):
  LRUFP.new_accepts(~U32, cap, h0, h1)

law lru_fast_u32_spec_new_accepts:
  for +cap: U32
  for +h0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}
  {LRUFS.new(U32, cap) == Done{LRUFS.LM{cap, LRUFS.zero_time(), Nil{}, LRUFT.zero_metrics()}} : Result<&2, &2, String, LRUFS.Model<U32>>}
def lru_fast_u32_spec_new_accepts(cap, h0, h1):
  LRUFP.spec_new_accepts(U32, cap, h0, h1)

law lru_fast_u32_new_rejects_zero:
  {LRUF.new(~U32, 0) == LRUF.Rejected{"capacity must be positive"} : LRUF.Made<U32>}
def lru_fast_u32_new_rejects_zero():
  LRUFP.new_zero(~U32)

law lru_fast_u32_spec_new_rejects_zero:
  {LRUFS.new(U32, 0) == Fail{"capacity must be positive"} : Result<&2, &2, String, LRUFS.Model<U32>>}
def lru_fast_u32_spec_new_rejects_zero():
  LRUFP.spec_new_zero(U32)

law lru_fast_u32_new_rejects_reserved:
  {LRUF.new(~U32, 4294967295) == LRUF.Rejected{"size must not be 0XFFFFFFFF"} : LRUF.Made<U32>}
def lru_fast_u32_new_rejects_reserved():
  LRUFP.new_reserved(~U32)

law lru_fast_u32_spec_new_rejects_reserved:
  {LRUFS.new(U32, 4294967295) == Fail{"size must not be 0XFFFFFFFF"} : Result<&2, &2, String, LRUFS.Model<U32>>}
def lru_fast_u32_spec_new_rejects_reserved():
  LRUFP.spec_new_reserved(U32)

law lru_fast_u32_new:
  for +cap: U32
  {LRUFSH.model(~U32, LRUFSH.initial(~U32, cap)) == LRUFS.LM{cap, LRUFS.zero_time(), Nil{}, LRUFT.zero_metrics()} : LRUFS.Model<U32>}
def lru_fast_u32_new(cap):
  LRUFP.new_abs(~U32, cap)

law lru_fast_u32_new_invariant:
  for +cap: U32
  for +hc: {U32.is_eq(cap, 0) == False{} : Bool}
  {LRUFSH.good(~U32, LRUFSH.initial(~U32, cap)) == True{} : Bool}
def lru_fast_u32_new_invariant(cap, hc):
  LRUFP.new_inv(~U32, cap, hc)

law lru_fast_u32_step:
  for +sh: LRUFSH.Shadow<U32>
  for +op: LRUFE.Op<U32>
  for +h: {LRUFSH.good(~U32, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {LRUFTR.cb(U32, q, sh) == True{} : Bool}
  LRUFSP.StepOK(~U32, sh, op)
def lru_fast_u32_step(sh, op, h, q, hq, hc):
  LRUFP.step_ok(~U32, sh, op, h, q, hq, hc)

law lru_fast_u32_trace:
  for +cap: U32
  for +ops: List<&2, LRUFE.Op<U32>>
  for +hc0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {Nat.is_le(U32.to_nat(cap), SCOM.pow2(q)) == True{} : Bool}
  for +hops: {LRUFTR.all_ok(U32, q, ops) == True{} : Bool}
  LRUFTR.TraceNew(~U32, cap, ops)
def lru_fast_u32_trace(cap, ops, hc0, q, hq, hc, hops):
  LRUFP.trace_new(~U32, cap, ops, hc0, q, hq, hc, hops)

law lru_fast_u32_trace_from:
  for +ops: List<&2, LRUFE.Op<U32>>
  for +sh: LRUFSH.Shadow<U32>
  for +h: {LRUFSH.good(~U32, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {LRUFTR.cb(U32, q, sh) == True{} : Bool}
  for +hops: {LRUFTR.all_ok(U32, q, ops) == True{} : Bool}
  LRUFTR.TraceOK(~U32, ops, sh)
def lru_fast_u32_trace_from(ops, sh, h, q, hq, hc, hops):
  LRUFP.trace_from(~U32, ops, sh, h, q, hq, hc, hops)

law lru_fast_string_new_is_the_constructor:
  for +cap: U32
  {LRUF.init(~String, cap) == LRUFSH.real(~String, LRUFSH.initial(~String, cap)) : LRUF.Fast<String>}
def lru_fast_string_new_is_the_constructor(cap):
  LRUFP.new_real(~String, cap)

law lru_fast_string_new_accepts:
  for +cap: U32
  for +h0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}
  {LRUF.new(~String, cap) == LRUF.Made{LRUF.init(~String, cap)} : LRUF.Made<String>}
def lru_fast_string_new_accepts(cap, h0, h1):
  LRUFP.new_accepts(~String, cap, h0, h1)

law lru_fast_string_spec_new_accepts:
  for +cap: U32
  for +h0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}
  {LRUFS.new(String, cap) == Done{LRUFS.LM{cap, LRUFS.zero_time(), Nil{}, LRUFT.zero_metrics()}} : Result<&2, &2, String, LRUFS.Model<String>>}
def lru_fast_string_spec_new_accepts(cap, h0, h1):
  LRUFP.spec_new_accepts(String, cap, h0, h1)

law lru_fast_string_new_rejects_zero:
  {LRUF.new(~String, 0) == LRUF.Rejected{"capacity must be positive"} : LRUF.Made<String>}
def lru_fast_string_new_rejects_zero():
  LRUFP.new_zero(~String)

law lru_fast_string_spec_new_rejects_zero:
  {LRUFS.new(String, 0) == Fail{"capacity must be positive"} : Result<&2, &2, String, LRUFS.Model<String>>}
def lru_fast_string_spec_new_rejects_zero():
  LRUFP.spec_new_zero(String)

law lru_fast_string_new_rejects_reserved:
  {LRUF.new(~String, 4294967295) == LRUF.Rejected{"size must not be 0XFFFFFFFF"} : LRUF.Made<String>}
def lru_fast_string_new_rejects_reserved():
  LRUFP.new_reserved(~String)

law lru_fast_string_spec_new_rejects_reserved:
  {LRUFS.new(String, 4294967295) == Fail{"size must not be 0XFFFFFFFF"} : Result<&2, &2, String, LRUFS.Model<String>>}
def lru_fast_string_spec_new_rejects_reserved():
  LRUFP.spec_new_reserved(String)

law lru_fast_string_new:
  for +cap: U32
  {LRUFSH.model(~String, LRUFSH.initial(~String, cap)) == LRUFS.LM{cap, LRUFS.zero_time(), Nil{}, LRUFT.zero_metrics()} : LRUFS.Model<String>}
def lru_fast_string_new(cap):
  LRUFP.new_abs(~String, cap)

law lru_fast_string_new_invariant:
  for +cap: U32
  for +hc: {U32.is_eq(cap, 0) == False{} : Bool}
  {LRUFSH.good(~String, LRUFSH.initial(~String, cap)) == True{} : Bool}
def lru_fast_string_new_invariant(cap, hc):
  LRUFP.new_inv(~String, cap, hc)

law lru_fast_string_step:
  for +sh: LRUFSH.Shadow<String>
  for +op: LRUFE.Op<String>
  for +h: {LRUFSH.good(~String, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {LRUFTR.cb(String, q, sh) == True{} : Bool}
  LRUFSP.StepOK(~String, sh, op)
def lru_fast_string_step(sh, op, h, q, hq, hc):
  LRUFP.step_ok(~String, sh, op, h, q, hq, hc)

law lru_fast_string_trace:
  for +cap: U32
  for +ops: List<&2, LRUFE.Op<String>>
  for +hc0: {U32.is_eq(cap, 0) == False{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {Nat.is_le(U32.to_nat(cap), SCOM.pow2(q)) == True{} : Bool}
  for +hops: {LRUFTR.all_ok(String, q, ops) == True{} : Bool}
  LRUFTR.TraceNew(~String, cap, ops)
def lru_fast_string_trace(cap, ops, hc0, q, hq, hc, hops):
  LRUFP.trace_new(~String, cap, ops, hc0, q, hq, hc, hops)

law lru_fast_string_trace_from:
  for +ops: List<&2, LRUFE.Op<String>>
  for +sh: LRUFSH.Shadow<String>
  for +h: {LRUFSH.good(~String, sh) == True{} : Bool}
  for +q: Nat
  for +hq: {Nat.is_le(q, 31n) == True{} : Bool}
  for +hc: {LRUFTR.cb(String, q, sh) == True{} : Bool}
  for +hops: {LRUFTR.all_ok(String, q, ops) == True{} : Bool}
  LRUFTR.TraceOK(~String, ops, sh)
def lru_fast_string_trace_from(ops, sh, h, q, hq, hc, hops):
  LRUFP.trace_from(~String, ops, sh, h, q, hq, hc, hops)

law lru_fast_u32_shadow_unique:
  for +a: LRUFSH.Shadow<U32>
  for +b: LRUFSH.Shadow<U32>
  for +ga: {LRUFSH.good(~U32, a) == True{} : Bool}
  for +gb: {LRUFSH.good(~U32, b) == True{} : Bool}
  for +e: {LRUFSH.real(~U32, a) == LRUFSH.real(~U32, b) : LRUF.Fast<U32>}
  {a == b : LRUFSH.Shadow<U32>}
def lru_fast_u32_shadow_unique(a, b, ga, gb, e):
  LRUFP.shadow_unique(~U32, a, b, ga, gb, e)

law lru_fast_string_shadow_unique:
  for +a: LRUFSH.Shadow<String>
  for +b: LRUFSH.Shadow<String>
  for +ga: {LRUFSH.good(~String, a) == True{} : Bool}
  for +gb: {LRUFSH.good(~String, b) == True{} : Bool}
  for +e: {LRUFSH.real(~String, a) == LRUFSH.real(~String, b) : LRUF.Fast<String>}
  {a == b : LRUFSH.Shadow<String>}
def lru_fast_string_shadow_unique(a, b, ga, gb, e):
  LRUFP.shadow_unique(~String, a, b, ga, gb, e)
