import Base
import ../../../src/containers/priority_queue.bend as P2
import ../../../src/containers/binary_heap.bend as K2
import ../../../src/containers/types/binary_heap.bend as E2

# src/containers/priority_queue.bend: a binary heap behind the queue interface (put = push, get = pop, qsize = length).

def priority_queue_put(q: K2.Heap<U32>, +v: U32) -> {P2.put(~U32, ~U32.cmp, q, v) == K2.push(~U32, ~U32.cmp, q, v) : K2.Heap<U32>}:
  {==}

def priority_queue_get(q: K2.Heap<U32>) -> {P2.get(~U32, ~U32.cmp, q) == K2.pop(~U32, ~U32.cmp, q) : K2.Heap<U32> & Result<&2, &2, E2.Error, U32>}:
  {==}

def priority_queue_qsize(q: K2.Heap<U32>) -> {P2.qsize(~U32, q) == K2.length(~U32, q) : K2.Heap<U32> & Nat}:
  {==}
