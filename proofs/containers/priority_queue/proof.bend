import Base
import ../../../src/containers/priority_queue.bend as P2
import ../../../src/containers/binary_heap.bend as K2
import ../../../src/containers/types/binary_heap.bend as E2
import ../../../spec/containers/priority_queue.bend as S
import ../../../spec/containers/binary_heap.bend as HS
import ../../../spec/lib/order.bend as SO
import ../binary_heap/proof.bend as UP

# src/containers/priority_queue.bend: a binary heap behind the queue interface (put = push, get = pop, qsize = length).

def priority_queue_put(q: K2.Heap<U32>, +v: U32) -> {P2.put(~U32, ~U32.cmp, q, v) == K2.push(~U32, ~U32.cmp, q, v) : K2.Heap<U32>}:
  {==}

def priority_queue_get(q: K2.Heap<U32>) -> {P2.get(~U32, ~U32.cmp, q) == K2.pop(~U32, ~U32.cmp, q) : K2.Heap<U32> & Result<&2, &2, E2.Error, U32>}:
  {==}

def priority_queue_qsize(q: K2.Heap<U32>) -> {P2.qsize(~U32, q) == K2.length(~U32, q) : K2.Heap<U32> & Nat}:
  {==}

# ==== the contract of priority_queue (stated in spec/containers/priority_queue.bend) ====================

def new_is(~A: Data) -> {P2.new(~A) == K2.new(~A) : K2.Heap<A>}:
  {==}

def qsize_is(~A: Data, h: K2.Heap<A>) -> {P2.qsize(~A, h) == K2.length(~A, h) : K2.Heap<A> & Nat}:
  {==}

def put_is(~A: Data, ~cmp: A -> A -> Cmp, h: K2.Heap<A>, x: A) -> {P2.put(~A, ~cmp, h, x) == K2.push(~A, ~cmp, h, x) : K2.Heap<A>}:
  {==}

def peek_is(~A: Data, h: K2.Heap<A>) -> {P2.peek(~A, h) == K2.peek(~A, h) : K2.Heap<A> & Result<&2, &2, E2.Error, A>}:
  {==}

def get_is(~A: Data, ~cmp: A -> A -> Cmp, h: K2.Heap<A>) -> {P2.get(~A, ~cmp, h) == K2.pop(~A, ~cmp, h) : K2.Heap<A> & Result<&2, &2, E2.Error, A>}:
  {==}

def from_list_is(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> {P2.from_list(~A, ~cmp, xs) == K2.from_list(~A, ~cmp, xs) : K2.Heap<A>}:
  {==}

def to_sorted_list_is(~A: Data, ~cmp: A -> A -> Cmp, h: K2.Heap<A>) -> {P2.to_sorted_list(~A, ~cmp, h) == K2.to_sorted_list(~A, ~cmp, h) : K2.Heap<A> & List<&2, A>}:
  {==}

# ---- the binary_heap's contract, carried: every clause is proved by the binary_heap ----

def length_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Length.length_result(~A, ~cmp, xs):
  UP.length_result(~A, ~cmp, xs)

def length_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Length.length_frame(~A, ~cmp, xs):
  UP.length_frame(~A, ~cmp, xs)

def push_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +x: A) -> S.Insert.push_length(~A, ~cmp, xs, x):
  UP.push_length(~A, ~cmp, xs, x)

def push_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A) -> S.Insert.push_bag(~A, ~cmp, ~o, xs, x):
  UP.push_bag(~A, ~cmp, ~o, xs, x)

def push_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A, +hs: {HS.sorted(~A, ~cmp, xs) == True{} : Bool}) -> S.Insert.push_sorted(~A, ~cmp, ~o, xs, x, hs):
  UP.push_sorted(~A, ~cmp, ~o, xs, x, hs)

def peek_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.First_Element.peek_min(~A, ~cmp, h, t, hs):
  UP.peek_min(~A, ~cmp, h, t, hs)

def peek_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.First_Element.peek_frame(~A, ~cmp, xs):
  UP.peek_frame(~A, ~cmp, xs)

def peek_empty(~A: Data, ~cmp: A -> A -> Cmp) -> S.First_Element.peek_empty(~A, ~cmp):
  UP.peek_empty(~A, ~cmp)

def pop_length(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> S.Delete_First.pop_length(~A, ~cmp, h, t):
  UP.pop_length(~A, ~cmp, h, t)

def pop_result(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> S.Delete_First.pop_result(~A, ~cmp, h, t):
  UP.pop_result(~A, ~cmp, h, t)

def pop_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.Delete_First.pop_min(~A, ~cmp, h, t, hs):
  UP.pop_min(~A, ~cmp, h, t, hs)

def pop_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.Delete_First.pop_bag(~A, ~cmp, ~o, h, t, hs):
  UP.pop_bag(~A, ~cmp, ~o, h, t, hs)

def pop_empty(~A: Data, ~cmp: A -> A -> Cmp) -> S.Delete_First.pop_empty(~A, ~cmp):
  UP.pop_empty(~A, ~cmp)

def from_list_model(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_model(~A, ~cmp, xs, ys):
  UP.from_list_model(~A, ~cmp, xs, ys)

def from_list_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_length(~A, ~cmp, xs, ys):
  UP.from_list_length(~A, ~cmp, xs, ys)

def from_list_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_sorted(~A, ~cmp, ~o, xs, ys):
  UP.from_list_sorted(~A, ~cmp, ~o, xs, ys)

def to_sorted_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Elements.to_sorted_result(~A, ~cmp, xs):
  UP.to_sorted_result(~A, ~cmp, xs)

def to_sorted_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Elements.to_sorted_frame(~A, ~cmp, xs):
  UP.to_sorted_frame(~A, ~cmp, xs)

