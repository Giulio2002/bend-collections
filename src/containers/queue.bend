import Base
import ./types/queue.bend as E

# Two-list FIFO queue: front ++ reverse(back). Reverse back only when front
# is empty. Enqueue/dequeue/peek are amortized O(1) on consumed histories.
# length is cached; to_list is O(n). Independent of the deque and DLL.
type Queue<-T: Data> is Type:
  QU{front: List<&2, T>, back: List<&2, T>, count: Nat}

def new(~T: Data) -> Queue<T>:
  QU{Nil{}, Nil{}, 0n}

def length(~T: Data, q: Queue<T>) -> Queue<T> & Nat:
  QU{f, b, +n} = q
  (QU{f, b, n}, n)

def enqueue(~T: Data, q: Queue<T>, x: T) -> Queue<T>:
  QU{f, b, n} = q
  QU{f, Con{x, b}, 1n+n}

def ready(~T: Data, q: Queue<T>) -> Queue<T>:
  match q:
    case QU{Nil{}, b, n}:
      QU{List.reverse(&2, T, b), Nil{}, n}
    case QU{Con{x, f}, b, n}:
      QU{Con{x, f}, b, n}

def dequeue_ready(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  match q:
    case QU{Nil{}, b, n}:
      (QU{Nil{}, b, n}, Fail{E.EmptyQueue{}})
    case QU{Con{x, f}, b, n}:
      (QU{f, b, Nat.sub(n, 1n)}, Done{x})

def peek_ready(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  match q:
    case QU{Nil{}, b, n}:
      (QU{Nil{}, b, n}, Fail{E.EmptyQueue{}})
    case QU{Con{+x, f}, b, n}:
      (QU{Con{x, f}, b, n}, Done{x})

def dequeue(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  dequeue_ready(~T, ready(~T, q))

def peek(~T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>:
  peek_ready(~T, ready(~T, q))

def to_list(~T: Data, q: Queue<T>) -> Queue<T> & List<&2, T>:
  QU{+f, +b, n} = q
  (QU{f, b, n}, List.append(&2, T, f, List.reverse(&2, T, b)))

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
