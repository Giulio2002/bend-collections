import Base
import ./src/lifo_queue.bend as P0
import ./src/stack.bend as K0
import ./types/stack.bend as E0
import ./src/simple_queue.bend as P1
import ./src/queue.bend as K1
import ./types/queue.bend as E1
import ./src/priority_queue.bend as P2
import ./src/binary_heap.bend as K2
import ./types/binary_heap.bend as E2

def lifo_queue_put(q: K0.Stack<U32>, +v: U32) -> {P0.put(~U32, q, v) == K0.push(~U32, q, v) : K0.Stack<U32>}:
  {==}

def lifo_queue_get(q: K0.Stack<U32>) -> {P0.get(~U32, q) == K0.pop(~U32, q) : K0.Stack<U32> & Result<&2, &2, E0.Error, U32>}:
  {==}

def lifo_queue_qsize(q: K0.Stack<U32>) -> {P0.qsize(~U32, q) == K0.length(~U32, q) : K0.Stack<U32> & Nat}:
  {==}

def simple_queue_put(q: K1.Queue<U32>, +v: U32) -> {P1.put(~U32, q, v) == K1.enqueue(~U32, q, v) : K1.Queue<U32>}:
  {==}

def simple_queue_get(q: K1.Queue<U32>) -> {P1.get(~U32, q) == K1.dequeue(~U32, q) : K1.Queue<U32> & Result<&2, &2, E1.Error, U32>}:
  {==}

def simple_queue_qsize(q: K1.Queue<U32>) -> {P1.qsize(~U32, q) == K1.length(~U32, q) : K1.Queue<U32> & Nat}:
  {==}

def priority_queue_put(q: K2.Heap<U32>, +v: U32) -> {P2.put(~U32, ~U32.cmp, q, v) == K2.push(~U32, ~U32.cmp, q, v) : K2.Heap<U32>}:
  {==}

def priority_queue_get(q: K2.Heap<U32>) -> {P2.get(~U32, ~U32.cmp, q) == K2.pop(~U32, ~U32.cmp, q) : K2.Heap<U32> & Result<&2, &2, E2.Error, U32>}:
  {==}

def priority_queue_qsize(q: K2.Heap<U32>) -> {P2.qsize(~U32, q) == K2.length(~U32, q) : K2.Heap<U32> & Nat}:
  {==}
