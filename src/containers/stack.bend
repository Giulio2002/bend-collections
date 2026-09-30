import Base
import ./types/stack.bend as E
import ./dynamic_array.bend as DA

# Stack of array chunks. The top chunk holds its `n` elements, bottom first,
# in the first n slots of an array of 2^d Maybe slots (the rest None); it
# grows by doubling up to 2^cmax() slots, then a new chunk starts on top of
# it. `count` is the whole stack's length. Push/pop/peek/length are O(1)
# amortized, push never fails, and to_list reads the chunks' slots into a
# fresh list (nothing shared is walked). Empty chunks are never kept, so the
# empty stack allocates nothing.
type Stack<-T: Data> is Type:
  SE{}
  ST{d: Nat, n: Nat, arr: Array<Maybe<&2, T>>, count: Nat, rest: Stack<T>}

# the largest chunk is 2^cmax() slots
def cmax() -> Nat:
  20n

def new(~T: Data) -> Stack<T>:
  SE{}

def length(~T: Data, s: Stack<T>) -> Stack<T> & Nat:
  match s:
    case SE{}:
      (SE{}, 0n)
    case ST{d, n, a, +c, r}:
      (ST{d, n, a, c, r}, c)

# ---- push ----

def push_new(~T: Data, +c: Nat, s: Stack<T>, x: T) -> Stack<T>:
  ST{0n, 1n, ALeaf{Some{x}}, 1n+c, s}

def push_full(~T: Data, +d: Nat, +n: Nat, a: Array<Maybe<&2, T>>, +c: Nat, r: Stack<T>, x: T, grow: Bool) -> Stack<T>:
  match grow:
    case True{}:
      ST{1n+d, 1n+n, Array.set(Maybe<&2, T>, DA.grown(T, d, a), U32.from_nat(n), Some{x}), 1n+c, r}
    case False{}:
      push_new(~T, c, ST{d, n, a, c, r}, x)

def push_room(~T: Data, +d: Nat, +n: Nat, a: Array<Maybe<&2, T>>, +c: Nat, r: Stack<T>, x: T, room: Bool) -> Stack<T>:
  match room:
    case True{}:
      ST{d, 1n+n, Array.set(Maybe<&2, T>, a, U32.from_nat(n), Some{x}), 1n+c, r}
    case False{}:
      push_full(~T, d, n, a, c, r, x, Nat.is_lt(d, cmax()))

def push(~T: Data, s: Stack<T>, x: T) -> Stack<T>:
  match s:
    case SE{}:
      push_new(~T, 0n, SE{}, x)
    case ST{+d, +n, a, +c, r}:
      push_room(~T, d, n, a, c, r, x, Nat.is_lt(n, DA.pow2(d)))

# ---- pop / peek ----

def pop_fin(~T: Data, +d: Nat, +m: Nat, +c: Nat, r: Stack<T>, q: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match m q:
    case 0n Tuple{a, Some{x}}:
      (r, Done{x})
    case 1n+k Tuple{a, Some{x}}:
      (ST{d, 1n+k, a, Nat.sub(c, 1n), r}, Done{x})
    case 0n Tuple{a, None{}}:
      (ST{d, 0n, a, c, r}, Fail{E.EmptyStack{}})
    case 1n+k Tuple{a, None{}}:
      (ST{d, 1n+k, a, c, r}, Fail{E.EmptyStack{}})

def pop(~T: Data, s: Stack<T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match s:
    case SE{}:
      (SE{}, Fail{E.EmptyStack{}})
    case ST{+d, 0n, a, c, r}:
      (ST{d, 0n, a, c, r}, Fail{E.EmptyStack{}})
    case ST{+d, 1n+ +m, a, +c, r}:
      pop_fin(~T, d, m, c, r, Array.swap(Maybe<&2, T>, a, U32.from_nat(m), None{}))

def peek_fin(~T: Data, +d: Nat, +n: Nat, +c: Nat, r: Stack<T>, q: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match q:
    case Tuple{a, Some{x}}:
      (ST{d, n, a, c, r}, Done{x})
    case Tuple{a, None{}}:
      (ST{d, n, a, c, r}, Fail{E.EmptyStack{}})

def peek(~T: Data, s: Stack<T>) -> Stack<T> & Result<&2, &2, E.Error, T>:
  match s:
    case SE{}:
      (SE{}, Fail{E.EmptyStack{}})
    case ST{+d, 0n, a, c, r}:
      (ST{d, 0n, a, c, r}, Fail{E.EmptyStack{}})
    case ST{+d, 1n+ +m, a, +c, r}:
      peek_fin(~T, d, 1n+m, c, r, Array.get(Maybe<&2, T>, a, U32.from_nat(m)))

# ---- to_list: each chunk's slots, bottom up, consed onto the rest's list ----

def cons_some(~T: Data, x: Maybe<&2, T>, acc: List<&2, T>) -> List<&2, T>:
  match x:
    case None{}:
      acc
    case Some{v}:
      Con{v, acc}

# reads slots i .. i + k (the pair holds slot i), consing each onto acc
def tl_go(~T: Data, k: Nat, +i: Nat, acc: List<&2, T>, q: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & List<&2, T>:
  match k q:
    case 0n Tuple{a, x}:
      (a, cons_some(~T, x, acc))
    case 1n+ +p Tuple{a, x}:
      tl_go(~T, p, 1n+i, cons_some(~T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(1n+i)))

def tl_fin(~T: Data, +d: Nat, +n: Nat, +c: Nat, r: Stack<T>, q: Array<Maybe<&2, T>> & List<&2, T>) -> Stack<T> & List<&2, T>:
  (a, xs) = q
  (ST{d, n, a, c, r}, xs)

def tl_chunk(~T: Data, +d: Nat, +n: Nat, a: Array<Maybe<&2, T>>, +c: Nat, q: Stack<T> & List<&2, T>) -> Stack<T> & List<&2, T>:
  match n q:
    case 0n Tuple{r, ys}:
      (ST{d, 0n, a, c, r}, ys)
    case 1n+ +m Tuple{r, ys}:
      tl_fin(~T, d, 1n+m, c, r, tl_go(~T, m, 0n, ys, Array.get(Maybe<&2, T>, a, U32.from_nat(0n))))

def to_list(~T: Data, s: Stack<T>) -> Stack<T> & List<&2, T>:
  match s:
    case SE{}:
      (SE{}, Nil{})
    case ST{+d, +n, a, +c, r}:
      tl_chunk(~T, d, n, a, c, to_list(~T, r))

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
