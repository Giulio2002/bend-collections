import Base
import ./lib/logic.bend as L
import ./lib/list.bend as LL
import ./lib/nat.bend as N
import ./lib/array.bend as AR
import ./lib/order.bend as O
import ./spec/common.bend as SC
import ./spec/binary_heap.bend as S
import ../src/containers/binary_heap.bend as H
import ../src/containers/types/binary_heap.bend as E
import ./binary_heap/state.bend as ST
import ./binary_heap/steps.bend as SP
import ./binary_heap/trace.bend as TR

# Binary heap: public proof entry point.
#   representation  a PACKED Base.Array block, element i with children 2i+1
#                   and 2i+2 (src/binary_heap.bend). The block is linear, so
#                   -- as in proofs/dynamic_array, proofs/bitset and
#                   proofs/deque -- every law is about the heap BUILT from a
#                   Data mirror tree (ST.real of a shadow).
#   abstraction     ST.model / ST.abs (the sorted multiset of the occupied
#                   slots; ST.abs reads an actual block through AR.freeze)
#   invariant       ST.good / ST.Inv (perfect block, elements exactly in
#                   [0, size), heap order over them, size <= 2^depth)
#   operations      SP.step_ok (every operation, errors included)
#   traces          trace_from / trace_new (arbitrary finite op lists)
#
# Laws are templates over a comparator ~cmp with total-order laws
# ~o : O.Order(~A, ~cmp); each is instantiated and thereby checked below for
# (U32, U32.cmp, O.u32_order) and (String, String.order, O.string_order), the
# instances src/ exposes.
#
# The capacity condition of the representation, in terms of the heap's
# SIZE: size + (elements the operations can add) < 2^q with q <= 31. A push
# doubles the block only when it is full, and then 2^depth = size < 2^q
# forces depth < 31, so every slot index stays a representable U32 (Base
# arrays have at most 2^31 slots). It is a premise only of the step and
# trace laws, it does not bound the length of a trace, and every other law
# holds at every state satisfying the invariant.

# ---- the constructor ----

def new_real(~A: Data, ~cmp: A -> A -> Cmp) -> {H.new(~A) == ST.real(~A, ST.initial(~A)) : H.Heap<A>}:
  ST.new_real(~A)

def new_inv(~A: Data, ~cmp: A -> A -> Cmp) -> {ST.good(~A, ~cmp, ST.initial(~A)) == True{} : Bool}:
  ST.new_good(~A, ~cmp)

def new_abs(~A: Data, ~cmp: A -> A -> Cmp) -> {ST.model(~A, ~cmp, ST.initial(~A)) == Nil{} : List<&2, A>}:
  ST.new_model(~A, ~cmp)

# ---- every operation (errors included), on every reachable representation ----

def step_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), sh: ST.Shadow<A>, op: E.Op<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), SP.pushcost(~A, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~A, ~cmp, sh, op):
  SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, room)

# The abstraction of an actual heap is the model of its shadow: the laws
# above, stated on shadows, are laws about actual heaps.
def abs_real(~A: Data, ~cmp: A -> A -> Cmp, +sh: ST.Shadow<A>) -> {ST.abs(~A, ~cmp, ST.real(~A, sh)) == ST.model(~A, ~cmp, sh) : List<&2, A>}:
  ST.abs_real(~A, ~cmp, sh)

def new_heap_inv(~A: Data, ~cmp: A -> A -> Cmp) -> ST.Inv(~A, ~cmp, H.new(~A)):
  (ST.initial(~A), (ST.new_real(~A), ST.new_good(~A, ~cmp)))

# ---- arbitrary finite traces ----

def trace_from(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +sh0: ST.Shadow<A>, +g0: {ST.good(~A, ~cmp, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh0), TR.pushes(~A, ops)), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~A, ~cmp, ops, sh0):
  TR.trace_from(~A, ~cmp, ~o, ops, sh0, g0, q, hq, room)

def trace_new(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~A, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~A, ~cmp, ops, ST.initial(~A)):
  TR.trace_from(~A, ~cmp, ~o, ops, ST.initial(~A), ST.new_good(~A, ~cmp), q, hq, room)

# ---- checked instances ----

def u32_step_ok(sh: ST.Shadow<U32>, op: E.Op<U32>, +g: {ST.good(~U32, ~U32.cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~U32, sh), SP.pushcost(~U32, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~U32, ~U32.cmp, sh, op):
  step_ok(~U32, ~U32.cmp, ~O.u32_order, sh, op, g, q, hq, room)

def u32_trace(+ops: List<&2, E.Op<U32>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~U32, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~U32, ~U32.cmp, ops, ST.initial(~U32)):
  trace_new(~U32, ~U32.cmp, ~O.u32_order, ops, q, hq, room)

def u32_new_inv() -> ST.Inv(~U32, ~U32.cmp, H.new(~U32)):
  new_heap_inv(~U32, ~U32.cmp)

def string_step_ok(sh: ST.Shadow<String>, op: E.Op<String>, +g: {ST.good(~String, ~String.order, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~String, sh), SP.pushcost(~String, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~String, ~String.order, sh, op):
  step_ok(~String, ~String.order, ~O.string_order, sh, op, g, q, hq, room)

def string_trace(+ops: List<&2, E.Op<String>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~String, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~String, ~String.order, ops, ST.initial(~String)):
  trace_new(~String, ~String.order, ~O.string_order, ops, q, hq, room)

def string_new_inv() -> ST.Inv(~String, ~String.order, H.new(~String)):
  new_heap_inv(~String, ~String.order)
