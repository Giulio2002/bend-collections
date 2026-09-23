import Base
import ../../../src/containers/lifo_queue.bend as P0
import ../../../src/containers/stack.bend as K0
import ../../../src/containers/types/stack.bend as E0

# src/containers/lifo_queue.bend: a stack behind the queue interface (put = push, get = pop, qsize = length).

def lifo_queue_put(q: K0.Stack<U32>, +v: U32) -> {P0.put(~U32, q, v) == K0.push(~U32, q, v) : K0.Stack<U32>}:
  {==}

def lifo_queue_get(q: K0.Stack<U32>) -> {P0.get(~U32, q) == K0.pop(~U32, q) : K0.Stack<U32> & Result<&2, &2, E0.Error, U32>}:
  {==}

def lifo_queue_qsize(q: K0.Stack<U32>) -> {P0.qsize(~U32, q) == K0.length(~U32, q) : K0.Stack<U32> & Nat}:
  {==}
