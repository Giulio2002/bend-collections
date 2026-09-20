import Base
import ./lib/logic.bend as L
import ./lib/order.bend as O
import ../spec/binary_heap.bend as S
import ../src/binary_heap.bend as H
import ../types/binary_heap.bend as E
import ./binary_heap/multiset.bend as M
import ./binary_heap/tree.bend as TR
import ./binary_heap/steps.bend as HS
import ./binary_heap/trace.bend as HT

# Binary heap: public proof entry point. Laws are templates over a comparator
# ~cmp with total-order laws ~o : O.Order(~A, ~cmp); each is instantiated and
# thereby checked below for (U32, U32.cmp, O.u32_order) and
# (String, String.order, O.string_order), the instances src/ exposes.
#   abstraction  HS.abs (sorted multiset of all elements)
#   invariant    HS.inv (exact size, heap order)

def new_abs(~A: Data, ~cmp: A -> A -> Cmp) -> {HS.abs(~A, ~cmp, H.new(A)) == Nil{} : List<&2, A>}:
  {==}

def new_inv(~A: Data, ~cmp: A -> A -> Cmp) -> {HS.inv(~A, ~cmp, H.new(A)) == True{} : Bool}:
  {==}

def step_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +h: H.Heap<A>, +op: E.Op<A>, +g: {HS.inv(~A, ~cmp, h) == True{} : Bool}) -> HS.StepOK(~A, ~cmp, h, op):
  HS.step_ok(~A, ~cmp, ~o, h, op, g)

def trace_new(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>) -> {HT.view(~A, ~cmp, ~o, H.run(~A, ~cmp, ops, H.new(A))) == S.run(~A, ~cmp, ops, Nil{}) : List<&2, A> & List<&2, E.Obs<A>>}:
  HT.trace_from(~A, ~cmp, ~o, ops, H.new(A), {==})

def trace_new_inv(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>) -> {HS.inv(~A, ~cmp, Pair.fst(H.Heap<A>, List<&2, E.Obs<A>>, H.run(~A, ~cmp, ops, H.new(A)))) == True{} : Bool}:
  HT.inv_from(~A, ~cmp, ~o, ops, H.new(A), {==})

# ---- checked instances ----

def u32_step_ok(+h: H.Heap<U32>, +op: E.Op<U32>, +g: {HS.inv(~U32, ~U32.cmp, h) == True{} : Bool}) -> HS.StepOK(~U32, ~U32.cmp, h, op):
  step_ok(~U32, ~U32.cmp, ~O.u32_order, h, op, g)

def u32_trace(+ops: List<&2, E.Op<U32>>) -> {HT.view(~U32, ~U32.cmp, ~O.u32_order, H.run_u32(ops, H.new(U32))) == S.run(~U32, ~U32.cmp, ops, Nil{}) : List<&2, U32> & List<&2, E.Obs<U32>>}:
  trace_new(~U32, ~U32.cmp, ~O.u32_order, ops)

def u32_trace_inv(+ops: List<&2, E.Op<U32>>) -> {HS.inv(~U32, ~U32.cmp, Pair.fst(H.Heap<U32>, List<&2, E.Obs<U32>>, H.run_u32(ops, H.new(U32)))) == True{} : Bool}:
  trace_new_inv(~U32, ~U32.cmp, ~O.u32_order, ops)

def string_step_ok(+h: H.Heap<String>, +op: E.Op<String>, +g: {HS.inv(~String, ~String.order, h) == True{} : Bool}) -> HS.StepOK(~String, ~String.order, h, op):
  step_ok(~String, ~String.order, ~O.string_order, h, op, g)

def string_trace(+ops: List<&2, E.Op<String>>) -> {HT.view(~String, ~String.order, ~O.string_order, H.run_string(ops, H.new(String))) == S.run(~String, ~String.order, ops, Nil{}) : List<&2, String> & List<&2, E.Obs<String>>}:
  trace_new(~String, ~String.order, ~O.string_order, ops)

def string_trace_inv(+ops: List<&2, E.Op<String>>) -> {HS.inv(~String, ~String.order, Pair.fst(H.Heap<String>, List<&2, E.Obs<String>>, H.run_string(ops, H.new(String)))) == True{} : Bool}:
  trace_new_inv(~String, ~String.order, ~O.string_order, ops)
