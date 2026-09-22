import Base
import ./stack.bend as K
import ./types/stack.bend as E

# Single-threaded queue API; storage and algorithms are shared with stack.
def new(~T: Data) -> K.Stack<T>:
  K.new(~T)

def qsize(~T: Data, s: K.Stack<T>) -> K.Stack<T> & Nat:
  K.length(~T, s)

def put(~T: Data, s: K.Stack<T>, x: T) -> K.Stack<T>:
  K.push(~T, s, x)

def get(~T: Data, s: K.Stack<T>) -> K.Stack<T> & Result<&2, &2, E.Error, T>:
  K.pop(~T, s)

def peek(~T: Data, s: K.Stack<T>) -> K.Stack<T> & Result<&2, &2, E.Error, T>:
  K.peek(~T, s)

def to_list(~T: Data, s: K.Stack<T>) -> K.Stack<T> & List<&2, T>:
  K.to_list(~T, s)
