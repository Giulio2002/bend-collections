import Base
import ../../../src/containers/simple_queue.bend as P1
import ../../../src/containers/queue.bend as K1
import ../../../src/containers/types/queue.bend as E1

# src/containers/simple_queue.bend: a FIFO queue behind the queue interface (put = enqueue, get = dequeue, qsize = length).

def simple_queue_put(q: K1.Queue<U32>, +v: U32) -> {P1.put(~U32, q, v) == K1.enqueue(~U32, q, v) : K1.Queue<U32>}:
  {==}

def simple_queue_get(q: K1.Queue<U32>) -> {P1.get(~U32, q) == K1.dequeue(~U32, q) : K1.Queue<U32> & Result<&2, &2, E1.Error, U32>}:
  {==}

def simple_queue_qsize(q: K1.Queue<U32>) -> {P1.qsize(~U32, q) == K1.length(~U32, q) : K1.Queue<U32> & Nat}:
  {==}
