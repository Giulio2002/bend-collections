import Base
import ./internal/dlist_storage.bend as D
import ../types/internal_dlist.bend as H
import ../types/deque.bend as E

# Deque adapter over the shared indexed doubly linked list.
# End removals recycle slots; no handles escape this API. Storage follows
# peak occupancy, including long alternating push/pop histories.
type Deque<-T: Data> is Type:
  DQ{items: D.DList<T>}

def new(~T: Data) -> Deque<T>:
  DQ{D.new(~T, 0)}

def lift_nat(~T: Data, r: D.DList<T> & Nat) -> Deque<T> & Nat:
  (s, n) = r
  (DQ{s}, n)

def length(~T: Data, d: Deque<T>) -> Deque<T> & Nat:
  DQ{s} = d
  lift_nat(~T, D.length(~T, s))


def pushed(~T: Data, r: D.DList<T> & H.Handle) -> Deque<T>:
  (s, h) = r
  DQ{s}

def push_front(~T: Data, d: Deque<T>, x: T) -> Deque<T>:
  DQ{s} = d
  pushed(~T, D.push_front_free(~T, s, x))

def push_back(~T: Data, d: Deque<T>, x: T) -> Deque<T>:
  DQ{s} = d
  pushed(~T, D.push_back_free(~T, s, x))

def item(~T: Data, m: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match m:
    case None{}:
      Fail{E.EmptyDeque{}}
    case Some{x}:
      Done{x}

def lift(~T: Data, r: D.DList<T> & Maybe<&2, T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (s, m) = r
  (DQ{s}, item(~T, m))

def pop_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{s} = d
  lift(~T, D.pop_front_free(~T, s))

def pop_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{s} = d
  lift(~T, D.pop_back_free(~T, s))

def peek_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{s} = d
  lift(~T, D.peek_front(~T, s))

def peek_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{s} = d
  lift(~T, D.peek_back(~T, s))

def lift_list(~T: Data, r: D.DList<T> & List<&2, T>) -> Deque<T> & List<&2, T>:
  (s, xs) = r
  (DQ{s}, xs)

# ---- operation traces ----

def to_list(~T: Data, d: Deque<T>) -> Deque<T> & List<&2, T>:
  DQ{s} = d
  lift_list(~T, D.to_list(~T, s))


def obs_nat(~T: Data, r: Deque<T> & Nat) -> Deque<T> & E.Obs<T>:
  (d, n) = r
  (d, E.ONat{n})

def obs_item(~T: Data, r: Deque<T> & Result<&2, &2, E.Error, T>) -> Deque<T> & E.Obs<T>:
  (d, x) = r
  (d, E.OItem{x})

def obs_list(~T: Data, r: Deque<T> & List<&2, T>) -> Deque<T> & E.Obs<T>:
  (d, xs) = r
  (d, E.OList{xs})

def step(~T: Data, d: Deque<T>, op: E.Op<T>) -> Deque<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(~T, length(~T, d))
    case E.PushFront{+x}:
      (push_front(~T, d, x), E.OUnit{})
    case E.PushBack{+x}:
      (push_back(~T, d, x), E.OUnit{})
    case E.PopFront{}:
      obs_item(~T, pop_front(~T, d))
    case E.PopBack{}:
      obs_item(~T, pop_back(~T, d))
    case E.PeekFront{}:
      obs_item(~T, peek_front(~T, d))
    case E.PeekBack{}:
      obs_item(~T, peek_back(~T, d))
    case E.ToList{}:
      obs_list(~T, to_list(~T, d))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: Deque<T> & E.Obs<T>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, o) = r
  (d, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, acc) = st
  record(~T, acc, step(~T, d, op))

# Runs ops left to right; observations are accumulated newest-first.
def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, acc) = st
  (d, List.reverse(&2, E.Obs<T>, acc))

# Final state and the observation of every operation, in order.
def run(~T: Data, ops: List<&2, E.Op<T>>, d: Deque<T>) -> Deque<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (d, Nil{})))
