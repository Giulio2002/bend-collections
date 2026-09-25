import Base
import ./lib/lemmas/src/public.bend as LRUPub
import ./lib/lemmas/spec/clock.bend as LRUClock
import ./lib/lemmas/spec/cache.bend as LRUSpec
import ./lib/lemmas/proofs/public_trace.bend as LRUTrace
import ./lib/array.bend as AR
import ./lib/logic.bend as L
import ../spec/lib/common.bend as SC
import ../src/containers/dynamic_array.bend as DA
import ../spec/containers/dynamic_array.bend as DAS
import ../src/containers/types/dynamic_array.bend as DAT
import ./containers/dynamic_array/proof.bend as DAP
import ./containers/dynamic_array/state.bend as DAST
import ../src/containers/deque.bend as DQ
import ../spec/containers/deque.bend as DQS
import ../src/containers/types/deque.bend as DQT
import ./containers/deque/proof.bend as DQP
import ./containers/deque/state.bend as DQSH
import ./containers/deque/stepok.bend as DQK
import ./containers/deque/trace.bend as DQTR
import ../src/containers/queue.bend as QU
import ../spec/containers/queue.bend as QUS
import ../src/containers/types/queue.bend as QUT
import ./containers/queue/proof.bend as QUP
import ./containers/queue/state.bend as QUSH
import ./containers/queue/steps.bend as QUST
import ./containers/queue/trace.bend as QUTR
import ./lib/order.bend as O
import ../src/containers/binary_heap.bend as BH
import ../spec/containers/binary_heap.bend as BHS
import ../src/containers/types/binary_heap.bend as BHT
import ./containers/binary_heap/proof.bend as BHP
import ./containers/binary_heap/state.bend as BHSH
import ./containers/binary_heap/steps.bend as BHST
import ./containers/binary_heap/trace.bend as BHTR
import ../src/containers/bitset.bend as BI
import ../spec/lib/common.bend as SCOM
import ../spec/containers/bitset.bend as BIS
import ../src/containers/types/bitset.bend as BIT
import ./containers/bitset/proof.bend as BIP
import ./containers/bitset/state.bend as BIST
import ./containers/bitset/steps.bend as BISP
import ./containers/bitset/trace.bend as BITR
import ../src/containers/bitlist.bend as BLI
import ../src/containers/types/bitlist.bend as BLT
import ../spec/containers/bitlist.bend as BLS
import ./containers/bitlist/state.bend as BLST
import ./containers/bitlist/steps.bend as BLSP
import ./containers/bitlist/trace.bend as BLTR
import ./containers/bitlist/proof.bend as BLP
import ../spec/containers/balanced_search_tree/recursive.bend as BTS
import ../src/containers/types/balanced_search_tree.bend as BTT

# Public correctness and trace laws, stated over the real src/ APIs and the
# independent spec/ models. Each law is discharged by its structure's proof
# entry module (proofs/<id>.bend). PROOF.bend imports this file.

# ============================ retained LRU ============================

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
  DAST.Inv(T, Pair.fst(DA.DynArray<&2, T>, DAT.Obs<T>, DA.step(T, DAST.real(T, sh), op)))
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
  DAST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, DAT.Obs<T>>, DA.run(T, ops, DA.new(T))))
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
  DAST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, DAT.Obs<T>>, DA.run(T, ops, DA.with_limit(T, k))))
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
  DAST.Inv(U32, Pair.fst(DA.DynArray<&2, U32>, DAT.Obs<U32>, DA.step_at(~U32, DAST.real(U32, sh), op)))
def dynamic_array_step_at_invariant_u32(sh, op, g):
  DAP.step_at_preserves(~U32, sh, op, g)

law dynamic_array_trace_at_u32:
  for +ops: List<&2, DAT.Op<U32>>
  {DAP.view(U32, DA.run_at(~U32, ops, DA.new_at(~U32))) == DAS.run(U32, ops, DAS.new(U32)) : DAS.Model<U32> & List<&2, DAT.Obs<U32>>}
def dynamic_array_trace_at_u32(ops):
  DAP.trace_new_at(~U32, ops)

law dynamic_array_trace_at_invariant_u32:
  for +ops: List<&2, DAT.Op<U32>>
  DAST.Inv(U32, Pair.fst(DA.DynArray<&2, U32>, List<&2, DAT.Obs<U32>>, DA.run_at(~U32, ops, DA.new_at(~U32))))
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
  DAST.Inv(U32, Pair.fst(DA.DynArray<&2, U32>, List<&2, DAT.Obs<U32>>, DA.run_at(~U32, ops, DA.with_limit_at(~U32, k))))
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
  DAST.Inv(Nat, Pair.fst(DA.DynArray<&2, Nat>, DAT.Obs<Nat>, DA.step_at(~Nat, DAST.real(Nat, sh), op)))
def dynamic_array_step_at_invariant_nat(sh, op, g):
  DAP.step_at_preserves(~Nat, sh, op, g)

law dynamic_array_trace_at_nat:
  for +ops: List<&2, DAT.Op<Nat>>
  {DAP.view(Nat, DA.run_at(~Nat, ops, DA.new_at(~Nat))) == DAS.run(Nat, ops, DAS.new(Nat)) : DAS.Model<Nat> & List<&2, DAT.Obs<Nat>>}
def dynamic_array_trace_at_nat(ops):
  DAP.trace_new_at(~Nat, ops)

law dynamic_array_trace_at_invariant_nat:
  for +ops: List<&2, DAT.Op<Nat>>
  DAST.Inv(Nat, Pair.fst(DA.DynArray<&2, Nat>, List<&2, DAT.Obs<Nat>>, DA.run_at(~Nat, ops, DA.new_at(~Nat))))
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
  DAST.Inv(Nat, Pair.fst(DA.DynArray<&2, Nat>, List<&2, DAT.Obs<Nat>>, DA.run_at(~Nat, ops, DA.with_limit_at(~Nat, k))))
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
  DAST.Inv(String, Pair.fst(DA.DynArray<&2, String>, DAT.Obs<String>, DA.step_at(~String, DAST.real(String, sh), op)))
def dynamic_array_step_at_invariant_string(sh, op, g):
  DAP.step_at_preserves(~String, sh, op, g)

law dynamic_array_trace_at_string:
  for +ops: List<&2, DAT.Op<String>>
  {DAP.view(String, DA.run_at(~String, ops, DA.new_at(~String))) == DAS.run(String, ops, DAS.new(String)) : DAS.Model<String> & List<&2, DAT.Obs<String>>}
def dynamic_array_trace_at_string(ops):
  DAP.trace_new_at(~String, ops)

law dynamic_array_trace_at_invariant_string:
  for +ops: List<&2, DAT.Op<String>>
  DAST.Inv(String, Pair.fst(DA.DynArray<&2, String>, List<&2, DAT.Obs<String>>, DA.run_at(~String, ops, DA.new_at(~String))))
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
  DAST.Inv(String, Pair.fst(DA.DynArray<&2, String>, List<&2, DAT.Obs<String>>, DA.run_at(~String, ops, DA.with_limit_at(~String, k))))
def dynamic_array_trace_limited_at_invariant_string(k, ops):
  DAP.trace_with_limit_at_inv(~String, k, ops)

# ============================== deque =================================
# Two lists (src/containers/deque.bend): the laws are about the deque of a
# Data shadow Sh{front, back} (DQSH.real); model = front ++ reverse(back).
# No premise: any finite trace, any size. Restated at U32 and String.

law deque_u32_new:
  {DQSH.model(U32, DQSH.initial(U32)) == Nil{} : List<&2, U32>}
def deque_u32_new():
  DQP.new_abs(~U32)

law deque_u32_new_is_the_constructor:
  {DQ.new(~U32) == DQSH.real(U32, DQSH.initial(U32)) : DQ.Deque<U32>}
def deque_u32_new_is_the_constructor():
  DQP.new_real(~U32)

law deque_u32_step:
  for +sh: DQSH.Shadow<U32>
  for +op: DQT.Op<U32>
  DQK.StepOK(~U32, sh, op)
def deque_u32_step(sh, op):
  DQP.step_ok(~U32, sh, op)

law deque_u32_shadow_unique:
  for +a: DQSH.Shadow<U32>
  for +b: DQSH.Shadow<U32>
  for +e: {DQSH.real(U32, a) == DQSH.real(U32, b) : DQ.Deque<U32>}
  {a == b : DQSH.Shadow<U32>}
def deque_u32_shadow_unique(a, b, e):
  DQP.shadow_unique(~U32, a, b, e)

law deque_u32_trace:
  for +ops: List<&2, DQT.Op<U32>>
  DQTR.TraceOK(~U32, ops, DQSH.initial(U32))
def deque_u32_trace(ops):
  DQP.trace_new(~U32, ops)

law deque_string_new:
  {DQSH.model(String, DQSH.initial(String)) == Nil{} : List<&2, String>}
def deque_string_new():
  DQP.new_abs(~String)

law deque_string_new_is_the_constructor:
  {DQ.new(~String) == DQSH.real(String, DQSH.initial(String)) : DQ.Deque<String>}
def deque_string_new_is_the_constructor():
  DQP.new_real(~String)

law deque_string_step:
  for +sh: DQSH.Shadow<String>
  for +op: DQT.Op<String>
  DQK.StepOK(~String, sh, op)
def deque_string_step(sh, op):
  DQP.step_ok(~String, sh, op)

law deque_string_shadow_unique:
  for +a: DQSH.Shadow<String>
  for +b: DQSH.Shadow<String>
  for +e: {DQSH.real(String, a) == DQSH.real(String, b) : DQ.Deque<String>}
  {a == b : DQSH.Shadow<String>}
def deque_string_shadow_unique(a, b, e):
  DQP.shadow_unique(~String, a, b, e)

law deque_string_trace:
  for +ops: List<&2, DQT.Op<String>>
  DQTR.TraceOK(~String, ops, DQSH.initial(String))
def deque_string_trace(ops):
  DQP.trace_new(~String, ops)

# ============================== queue =================================
# Two lists (src/containers/queue.bend), independent of the deque; the
# same shadow form, no premise.

law queue_u32_new:
  {QUSH.model(U32, QUSH.initial(U32)) == Nil{} : List<&2, U32>}
def queue_u32_new():
  QUP.new_abs(~U32)

law queue_u32_new_is_the_constructor:
  {QU.new(~U32) == QUSH.real(U32, QUSH.initial(U32)) : QU.Queue<U32>}
def queue_u32_new_is_the_constructor():
  QUP.new_real(~U32)

law queue_u32_step:
  for +sh: QUSH.Shadow<U32>
  for +op: QUT.Op<U32>
  QUST.StepOK(~U32, sh, op)
def queue_u32_step(sh, op):
  QUP.step_ok(~U32, sh, op)

law queue_u32_shadow_unique:
  for +a: QUSH.Shadow<U32>
  for +b: QUSH.Shadow<U32>
  for +e: {QUSH.real(U32, a) == QUSH.real(U32, b) : QU.Queue<U32>}
  {a == b : QUSH.Shadow<U32>}
def queue_u32_shadow_unique(a, b, e):
  QUP.shadow_unique(~U32, a, b, e)

law queue_u32_trace:
  for +ops: List<&2, QUT.Op<U32>>
  QUTR.TraceOK(~U32, ops, QUSH.initial(U32))
def queue_u32_trace(ops):
  QUP.trace_new(~U32, ops)

law queue_string_new:
  {QUSH.model(String, QUSH.initial(String)) == Nil{} : List<&2, String>}
def queue_string_new():
  QUP.new_abs(~String)

law queue_string_new_is_the_constructor:
  {QU.new(~String) == QUSH.real(String, QUSH.initial(String)) : QU.Queue<String>}
def queue_string_new_is_the_constructor():
  QUP.new_real(~String)

law queue_string_step:
  for +sh: QUSH.Shadow<String>
  for +op: QUT.Op<String>
  QUST.StepOK(~String, sh, op)
def queue_string_step(sh, op):
  QUP.step_ok(~String, sh, op)

law queue_string_shadow_unique:
  for +a: QUSH.Shadow<String>
  for +b: QUSH.Shadow<String>
  for +e: {QUSH.real(String, a) == QUSH.real(String, b) : QU.Queue<String>}
  {a == b : QUSH.Shadow<String>}
def queue_string_shadow_unique(a, b, e):
  QUP.shadow_unique(~String, a, b, e)

law queue_string_trace:
  for +ops: List<&2, QUT.Op<String>>
  QUTR.TraceOK(~String, ops, QUSH.initial(String))
def queue_string_trace(ops):
  QUP.trace_new(~String, ops)

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

# ======================== legacy balanced_search_tree ========================
# The laws below apply to the retained recursive implementation only.
# New indexed TreeMap component laws are in TREE_MAP_COMPONENT_PROOF.bend.
# Red-black binary tree ordered map (reference/legacy_balanced_search_tree.bend). The
# proofs are templates over a comparator with total-order laws; the laws are
# stated at the two instances src/ exposes: (U32, U32.cmp) and
# (String, String.order). Values are an erased type. The invariant
# (strictly increasing keys, red-black balance, cached size) is kept by
# every operation, and balance is also restated in textbook form.

# ============================== bitlist ===============================

law bitlist_new_is_the_constructor:
  {BLI.new() == BLST.real(BLTR.initial(None{})) : BLI.Bitlist}
def bitlist_new_is_the_constructor():
  BLP.new_real()

law bitlist_new:
  {BLST.model(BLTR.initial(None{})) == BLS.new() : BLS.Model}
def bitlist_new():
  BLP.new_model()

law bitlist_with_limit:
  for +n: Nat
  {BLST.model(BLTR.initial(Some{n})) == BLS.with_limit(n) : BLS.Model}
def bitlist_with_limit(n):
  BLP.with_limit_model(n)

law bitlist_step:
  for +sh: BLST.Sh
  for +op: BLT.Op
  for +g: {BLST.good(sh) == True{} : Bool}
  BLSP.StepOK(sh, op)
def bitlist_step(sh, op, g):
  BLP.step_ok(sh, op, g)

law bitlist_trace:
  for +ops: List<&2, BLT.Op>
  BLTR.TraceOK(ops, BLTR.initial(None{}))
def bitlist_trace(ops):
  BLP.trace_new(ops)

law bitlist_trace_limited:
  for +n: Nat
  for +ops: List<&2, BLT.Op>
  BLTR.TraceOK(ops, BLTR.initial(Some{n}))
def bitlist_trace_limited(n, ops):
  BLP.trace_with_limit(n, ops)

law bitlist_from_bools:
  for +bs: List<&2, Bool>
  BLTR.FromOK(bs, BLTR.initial(None{}))
def bitlist_from_bools(bs):
  BLP.from_bools(bs)
