import Base
import ./deque.bend as DQ
import ../types/deque.bend as DE
import ../types/queue.bend as E

# FIFO queue: the back-in/front-out specialization of src/deque.bend
# (enqueue = push_back, dequeue = pop_front, peek = peek_front). It reuses the
# deque's ring buffer and costs; see src/deque.bend. dequeue/peek on an
# empty queue return Fail{EmptyQueue} and the queue unchanged.

type Queue<-T: Data> is Type:
  QU{items: DQ.Deque<T>}

def new(~T: Data) -> Queue<T>:
  QU{DQ.new(~T)}

def result_of(-T: Data, r: Result<&2, &2, DE.Error, T>) -> Result<&2, &2, E.Error, T>:
  match r:
    case Fail{e}:
      Fail{E.EmptyQueue{}}
    case Done{x}:
      Done{x}

def lift(~T: Data, r: DQ.Deque<T> & Result<&2, &2, DE.Error, T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  (d, x) = r
  (QU{d}, result_of(T, x))

def lift_nat(~T: Data, r: DQ.Deque<T> & Nat) -> Queue<T> & Nat:
  (d, n) = r
  (QU{d}, n)

def lift_list(~T: Data, r: DQ.Deque<T> & List<&2, T>) -> Queue<T> & List<&2, T>:
  (d, xs) = r
  (QU{d}, xs)

def length(~T: Data, q: Queue<T>) -> Queue<T> & Nat:
  QU{d} = q
  lift_nat(~T, DQ.length(~T, d))

def enqueue(~T: Data, q: Queue<T>, +x: T) -> Queue<T>:
  QU{d} = q
  QU{DQ.push_back(~T, d, x)}

def dequeue(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  QU{d} = q
  lift(~T, DQ.pop_front(~T, d))

def peek(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  QU{d} = q
  lift(~T, DQ.peek_front(~T, d))

def to_list(~T: Data, q: Queue<T>) -> Queue<T> & List<&2, T>:
  QU{d} = q
  lift_list(~T, DQ.to_list(~T, d))

# ---- operation traces ----

def obs_nat(~T: Data, r: Queue<T> & Nat) -> Queue<T> & E.Obs<T>:
  (q, n) = r
  (q, E.ONat{n})

def obs_item(~T: Data, r: Queue<T> & Result<&2, &2, E.Error, T>) -> Queue<T> & E.Obs<T>:
  (q, x) = r
  (q, E.OItem{x})

def obs_list(~T: Data, r: Queue<T> & List<&2, T>) -> Queue<T> & E.Obs<T>:
  (q, xs) = r
  (q, E.OList{xs})

def step(~T: Data, q: Queue<T>, op: E.Op<T>) -> Queue<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(~T, length(~T, q))
    case E.Enqueue{+x}:
      (enqueue(~T, q, x), E.OUnit{})
    case E.Dequeue{}:
      obs_item(~T, dequeue(~T, q))
    case E.Peek{}:
      obs_item(~T, peek(~T, q))
    case E.ToList{}:
      obs_list(~T, to_list(~T, q))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: Queue<T> & E.Obs<T>) -> Queue<T> & List<&2, E.Obs<T>>:
  (q, o) = r
  (q, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: Queue<T> & List<&2, E.Obs<T>>) -> Queue<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  record(~T, acc, step(~T, q, op))

def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: Queue<T> & List<&2, E.Obs<T>>) -> Queue<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: Queue<T> & List<&2, E.Obs<T>>) -> Queue<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  (q, List.reverse(&2, E.Obs<T>, acc))

def run(~T: Data, ops: List<&2, E.Op<T>>, q: Queue<T>) -> Queue<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (q, Nil{})))
