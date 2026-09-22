import Base
import ./binary_heap.bend as K
import ../types/binary_heap.bend as E

# Single-threaded queue API; storage and algorithms are shared with binary_heap.
def new(~A: Data) -> K.Heap<A>:
  K.new(~A)

def qsize(~A: Data, h: K.Heap<A>) -> K.Heap<A> & Nat:
  K.length(~A, h)

def put(~A: Data, ~cmp: A -> A -> Cmp, h: K.Heap<A>, x: A) -> K.Heap<A>:
  K.push(~A, ~cmp, h, x)

def peek(~A: Data, h: K.Heap<A>) -> K.Heap<A> & Result<&2, &2, E.Error, A>:
  K.peek(~A, h)

def get(~A: Data, ~cmp: A -> A -> Cmp, h: K.Heap<A>) -> K.Heap<A> & Result<&2, &2, E.Error, A>:
  K.pop(~A, ~cmp, h)

def from_list(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> K.Heap<A>:
  K.from_list(~A, ~cmp, xs)

def to_sorted_list(~A: Data, ~cmp: A -> A -> Cmp, h: K.Heap<A>) -> K.Heap<A> & List<&2, A>:
  K.to_sorted_list(~A, ~cmp, h)
