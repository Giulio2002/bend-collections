import Base
import ../types/stack.bend as E

# Stack over the native singly linked List, with a stored length.
# Push/pop/peek/length O(1); to_list shares immutable Data elements/list.
type Stack<-T: Data> is Type:
  ST{items: List<&2, T>, count: Nat}

def new(~T: Data) -> Stack<T>:
  ST{Nil{}, 0n}

def length(~T: Data, s: Stack<T>) -> Stack<T> & Nat:
  ST{xs, +n} = s
  (ST{xs, n}, n)

def push(~T: Data, s: Stack<T>, x: T) -> Stack<T>:
  ST{xs, n} = s
  ST{Con{x, xs}, 1n+n}

def pop(~T: Data, s: Stack<T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match s:
    case ST{Nil{}, n}:
      (ST{Nil{}, n}, Fail{E.EmptyStack{}})
    case ST{Con{x, xs}, n}:
      (ST{xs, Nat.sub(n, 1n)}, Done{x})

def peek(~T: Data, s: Stack<T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match s:
    case ST{Nil{}, n}:
      (ST{Nil{}, n}, Fail{E.EmptyStack{}})
    case ST{Con{+x, xs}, n}:
      (ST{Con{x, xs}, n}, Done{x})

def to_list(~T: Data, s: Stack<T>) -> Stack<T> & List<&2, T>:
  ST{+xs, n} = s
  (ST{xs, n}, xs)

# ---- operation traces ----

def obs_nat(~T: Data, r: Stack<T> & Nat) -> Stack<T> & E.Obs<T>:
  (q, n) = r
  (q, E.ONat{n})

def obs_item(~T: Data, r: Stack<T> & Result<&2, &2, E.Error, T>) -> Stack<T> & E.Obs<T>:
  (q, x) = r
  (q, E.OItem{x})

def obs_list(~T: Data, r: Stack<T> & List<&2, T>) -> Stack<T> & E.Obs<T>:
  (q, xs) = r
  (q, E.OList{xs})

def step(~T: Data, q: Stack<T>, op: E.Op<T>) -> Stack<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(~T, length(~T, q))
    case E.Push{+x}:
      (push(~T, q, x), E.OUnit{})
    case E.Pop{}:
      obs_item(~T, pop(~T, q))
    case E.Peek{}:
      obs_item(~T, peek(~T, q))
    case E.ToList{}:
      obs_list(~T, to_list(~T, q))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: Stack<T> & E.Obs<T>) -> Stack<T> & List<&2, E.Obs<T>>:
  (q, o) = r
  (q, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: Stack<T> & List<&2, E.Obs<T>>) -> Stack<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  record(~T, acc, step(~T, q, op))

def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: Stack<T> & List<&2, E.Obs<T>>) -> Stack<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: Stack<T> & List<&2, E.Obs<T>>) -> Stack<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  (q, List.reverse(&2, E.Obs<T>, acc))

def run(~T: Data, ops: List<&2, E.Op<T>>, q: Stack<T>) -> Stack<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (q, Nil{})))
