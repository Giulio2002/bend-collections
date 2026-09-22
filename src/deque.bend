import Base
import ../types/deque.bend as E

# Two-list deque: logical order is front ++ reverse(back).
# Rebalance only when the requested side is empty, moving half the other
# side. End operations are amortized O(1) along a consumed state history;
# a rebalance is O(n). to_list is O(n). No arrays, handles or DLL storage.
type Deque<-T: Data> is Type:
  DE{front: List<&2, T>, back: List<&2, T>, nf: Nat, nb: Nat}

def new(~T: Data) -> Deque<T>:
  DE{Nil{}, Nil{}, 0n, 0n}

def length(~T: Data, d: Deque<T>) -> Deque<T> & Nat:
  DE{f, b, +nf, +nb} = d
  (DE{f, b, nf, nb}, Nat.add(nf, nb))

def push_front(~T: Data, d: Deque<T>, x: T) -> Deque<T>:
  DE{f, b, nf, nb} = d
  DE{Con{x, f}, b, 1n+nf, nb}

def push_back(~T: Data, d: Deque<T>, x: T) -> Deque<T>:
  DE{f, b, nf, nb} = d
  DE{f, Con{x, b}, nf, 1n+nb}

# One split traversal; keep the near half, reverse the far half.
def split_cons(~T: Data, x: T, r: List<&2, T> & List<&2, T>) -> List<&2, T> & List<&2, T>:
  (keep, moved) = r
  (Con{x, keep}, moved)

def split(~T: Data, n: Nat, xs: List<&2, T>) -> List<&2, T> & List<&2, T>:
  match n xs:
    case 0n ys:
      (Nil{}, List.reverse(&2, T, ys))
    case 1n+p Nil{}:
      (Nil{}, Nil{})
    case 1n+p Con{x, tail}:
      split_cons(~T, x, split(~T, p, tail))

def front_split(~T: Data, +n: Nat, +half: Nat, r: List<&2, T> & List<&2, T>) -> Deque<T>:
  (keep, moved) = r
  DE{moved, keep, Nat.sub(n, half), half}

def back_split(~T: Data, +n: Nat, +half: Nat, r: List<&2, T> & List<&2, T>) -> Deque<T>:
  (keep, moved) = r
  DE{keep, moved, half, Nat.sub(n, half)}

def move_front(~T: Data, b: List<&2, T>, +n: Nat, +half: Nat) -> Deque<T>:
  front_split(~T, n, half, split(~T, half, b))

def move_back(~T: Data, f: List<&2, T>, +n: Nat, +half: Nat) -> Deque<T>:
  back_split(~T, n, half, split(~T, half, f))

def ready_front(~T: Data, d: Deque<T>) -> Deque<T>:
  match d:
    case DE{Nil{}, b, nf, +nb}:
      move_front(~T, b, nb, Nat.div(nb, 2n))
    case DE{Con{x, f}, b, nf, nb}:
      DE{Con{x, f}, b, nf, nb}

def ready_back(~T: Data, d: Deque<T>) -> Deque<T>:
  match d:
    case DE{f, Nil{}, +nf, nb}:
      move_back(~T, f, nf, Nat.div(nf, 2n))
    case DE{f, Con{x, b}, nf, nb}:
      DE{f, Con{x, b}, nf, nb}

def pop_front_ready(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{Nil{}, b, nf, nb}:
      (DE{Nil{}, b, nf, nb}, Fail{E.EmptyDeque{}})
    case DE{Con{x, f}, b, nf, nb}:
      (DE{f, b, Nat.sub(nf, 1n), nb}, Done{x})

def pop_back_ready(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{f, Nil{}, nf, nb}:
      (DE{f, Nil{}, nf, nb}, Fail{E.EmptyDeque{}})
    case DE{f, Con{x, b}, nf, nb}:
      (DE{f, b, nf, Nat.sub(nb, 1n)}, Done{x})

def peek_front_ready(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{Nil{}, b, nf, nb}:
      (DE{Nil{}, b, nf, nb}, Fail{E.EmptyDeque{}})
    case DE{Con{+x, f}, b, nf, nb}:
      (DE{Con{x, f}, b, nf, nb}, Done{x})

def peek_back_ready(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{f, Nil{}, nf, nb}:
      (DE{f, Nil{}, nf, nb}, Fail{E.EmptyDeque{}})
    case DE{f, Con{+x, b}, nf, nb}:
      (DE{f, Con{x, b}, nf, nb}, Done{x})

def pop_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  pop_front_ready(~T, ready_front(~T, d))

def pop_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  pop_back_ready(~T, ready_back(~T, d))

def peek_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  peek_front_ready(~T, ready_front(~T, d))

def peek_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  peek_back_ready(~T, ready_back(~T, d))

def to_list(~T: Data, d: Deque<T>) -> Deque<T> & List<&2, T>:
  DE{+f, +b, nf, nb} = d
  (DE{f, b, nf, nb}, List.append(&2, T, f, List.reverse(&2, T, b)))

# ---- operation traces ----

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
