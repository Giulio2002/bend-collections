import Base
import ./queue.bend as K
import ./types/queue.bend as E

# Single-threaded queue API; storage and algorithms are shared with queue.
def new(~T: Data) -> K.Queue<T>:
  K.new(~T)

def qsize(~T: Data, q: K.Queue<T>) -> K.Queue<T> & Nat:
  K.length(~T, q)

def put(~T: Data, q: K.Queue<T>, x: T) -> K.Queue<T>:
  K.enqueue(~T, q, x)

def get(~T: Data, q: K.Queue<T>) -> K.Queue<T> & Result<&2, &2, E.Error, T>:
  K.dequeue(~T, q)

def peek(~T: Data, q: K.Queue<T>) -> K.Queue<T> & Result<&2, &2, E.Error, T>:
  K.peek(~T, q)

def to_list(~T: Data, q: K.Queue<T>) -> K.Queue<T> & List<&2, T>:
  K.to_list(~T, q)
