import Base
import ../types/deque.bend as E

# Double-ended queue over a native Base.Array: a window of occupied slots
# inside a power-of-two block of slots.
#
# Representation: DQ{depth, cap, lo, len, slots} with cap = 2^depth kept in
# the record (recomputing 2^depth per operation would make every push cost
# O(depth)). `slots` is a Base.Array of
# 2^depth slots; the elements are slots [lo, lo + len), front first, so
# element j is slot lo + j. Slots outside the window hold None.
#
#   push_back   writes slot lo + len                       (O(1))
#   push_front  writes slot lo - 1                         (O(1))
#   pop_front   takes slot lo, moves the window right      (O(1))
#   pop_back    takes slot lo + len - 1                    (O(1))
#   peek_front  reads slot lo                              (O(1))
#   peek_back   reads slot lo + len - 1                    (O(1))
#   to_list     reads the len slots of the window          (O(len))
#
# When a push has no free slot at its end the block is doubled, which is one
# Base.Array node and one fresh empty half: a back push makes the old block
# the LEFT half (every index is unchanged), a front push makes it the RIGHT
# half (every index moves up by the old capacity 2^depth, so the new window
# starts at 2^depth - 1). Doubling gives 2^depth free slots at that end, so
# the amortized cost of a push is O(1). No element is ever copied and no
# index arithmetic is modular.
#
# Capacity: `depth` grows by one per doubling, so a deque of n elements uses
# depth <= n + 1 and the laws about pushes carry the representation's
# capacity condition (depth < 31, so every slot index is a representable U32
# and Base's index masking is the identity). See docs/API.md.
#
# Errors: pop/peek on an empty deque return Fail{EmptyDeque} and the deque
# unchanged.

type Deque<-T: Data> is Type:
  DQ{depth: Nat, cap: Nat, lo: Nat, len: Nat, slots: Array<Maybe<&2, T>>}

def max_depth() -> Nat:
  31n

# 2^d (structural doubling; Base Nat.pow is avoided, see docs/VALIDATION.md).
def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# n - 1 on a nonzero n (the capacity 2^d is never zero).
def dec1(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def empty_slots(-T: Data, +depth: Nat) -> Array<Maybe<&2, T>>:
  Array.new(Maybe<&2, T>, depth, None{})

def new(-T: Data) -> Deque<T>:
  DQ{0n, 1n, 0n, 0n, empty_slots(T, 0n)}

def length(-T: Data, d: Deque<T>) -> Deque<T> & Nat:
  DQ{dep, cp, lo, +len, a} = d
  (DQ{dep, cp, lo, len, a}, len)

def item(-T: Data, slot: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match slot:
    case None{}:
      Fail{E.EmptyDeque{}}
    case Some{x}:
      Done{x}

# ---- push_back ----

# The old block becomes the left half: every index is unchanged.
def grown_back(-T: Data, +depth: Nat, a: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{a, empty_slots(T, depth)}

# The old block becomes the right half: every index moves up by 2^depth.
def grown_front(-T: Data, +depth: Nat, a: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{empty_slots(T, depth), a}

def pb_room(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +len: Nat, a: Array<Maybe<&2, T>>, v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      DQ{dep, cp, lo, 1n+len, Array.set(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, len)), Some{v})}
    case False{}:
      DQ{1n+dep, Nat.double(cp), lo, 1n+len, Array.set(Maybe<&2, T>, grown_back(T, dep, a), U32.from_nat(Nat.add(lo, len)), Some{v})}

def push_back(-T: Data, d: Deque<T>, v: T) -> Deque<T>:
  DQ{+dep, +cp, +lo, +len, a} = d
  pb_room(T, dep, cp, lo, len, a, v, Nat.is_lt(Nat.add(lo, len), cp))

# ---- push_front ----

def pf_lo(-T: Data, +dep: Nat, +cp: Nat, lo: Nat, +len: Nat, a: Array<Maybe<&2, T>>, v: T) -> Deque<T>:
  match lo:
    case 0n:
      DQ{1n+dep, Nat.double(cp), dec1(cp), 1n+len, Array.set(Maybe<&2, T>, grown_front(T, dep, a), U32.from_nat(dec1(cp)), Some{v})}
    case 1n+ +k:
      DQ{dep, cp, k, 1n+len, Array.set(Maybe<&2, T>, a, U32.from_nat(k), Some{v})}

def push_front(-T: Data, d: Deque<T>, v: T) -> Deque<T>:
  DQ{+dep, +cp, lo, +len, a} = d
  pf_lo(T, dep, cp, lo, len, a, v)

# ---- pop_front / pop_back ----

def pop_f_fin(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +m: Nat, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, old) = r
  (DQ{dep, cp, 1n+lo, m, a}, item(T, old))

def pop_f_len(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      pop_f_fin(T, dep, cp, lo, m, Array.swap(Maybe<&2, T>, a, U32.from_nat(lo), None{}))

def pop_front(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  pop_f_len(T, dep, cp, lo, len, a)

def pop_b_fin(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +m: Nat, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, old) = r
  (DQ{dep, cp, lo, m, a}, item(T, old))

def pop_b_len(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      pop_b_fin(T, dep, cp, lo, m, Array.swap(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m)), None{}))

def pop_back(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  pop_b_len(T, dep, cp, lo, len, a)

# ---- peek_front / peek_back ----

def peek_fin(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +len: Nat, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, x) = r
  (DQ{dep, cp, lo, len, a}, item(T, x))

def peek_f_len(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(T, dep, cp, lo, 1n+m, Array.get(Maybe<&2, T>, a, U32.from_nat(lo)))

def peek_front(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  peek_f_len(T, dep, cp, lo, len, a)

def peek_b_len(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(T, dep, cp, lo, 1n+m, Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m))))

def peek_back(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  peek_b_len(T, dep, cp, lo, len, a)

# ---- to_list ----

def cons_mb(-T: Data, x: Maybe<&2, T>, acc: List<&2, T>) -> List<&2, T>:
  match x:
    case None{}:
      acc
    case Some{v}:
      Con{v, acc}

# k slots of the window are still to be read, the last of them first: the
# pair `r` is slot lo + k - 1, already read.
def tl_go(k: Nat, -T: Data, +lo: Nat, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & List<&2, T>:
  match k r:
    case 0n Tuple{a, x}:
      (a, acc)
    case 1n+ +m Tuple{a, x}:
      tl_go(m, T, lo, cons_mb(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, dec1(m)))))

def tl_done(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +len: Nat, r: Array<Maybe<&2, T>> & List<&2, T>) -> Deque<T> & List<&2, T>:
  (a, xs) = r
  (DQ{dep, cp, lo, len, a}, xs)

def tl_start(-T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & List<&2, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Nil{})
    case 1n+ +m:
      tl_done(T, dep, cp, lo, 1n+m, tl_go(1n+m, T, lo, Nil{}, Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m)))))

def to_list(-T: Data, d: Deque<T>) -> Deque<T> & List<&2, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  tl_start(T, dep, cp, lo, len, a)

# ---- operation traces ----

def obs_nat(-T: Data, r: Deque<T> & Nat) -> Deque<T> & E.Obs<T>:
  (d, n) = r
  (d, E.ONat{n})

def obs_item(-T: Data, r: Deque<T> & Result<&2, &2, E.Error, T>) -> Deque<T> & E.Obs<T>:
  (d, x) = r
  (d, E.OItem{x})

def obs_list(-T: Data, r: Deque<T> & List<&2, T>) -> Deque<T> & E.Obs<T>:
  (d, xs) = r
  (d, E.OList{xs})

def step(-T: Data, d: Deque<T>, op: E.Op<T>) -> Deque<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(T, length(T, d))
    case E.PushFront{x}:
      (push_front(T, d, x), E.OUnit{})
    case E.PushBack{x}:
      (push_back(T, d, x), E.OUnit{})
    case E.PopFront{}:
      obs_item(T, pop_front(T, d))
    case E.PopBack{}:
      obs_item(T, pop_back(T, d))
    case E.PeekFront{}:
      obs_item(T, peek_front(T, d))
    case E.PeekBack{}:
      obs_item(T, peek_back(T, d))
    case E.ToList{}:
      obs_list(T, to_list(T, d))

def record(-T: Data, acc: List<&2, E.Obs<T>>, r: Deque<T> & E.Obs<T>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, o) = r
  (d, Con{o, acc})

def step_acc(-T: Data, op: E.Op<T>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, acc) = st
  record(T, acc, step(T, d, op))

# Runs ops left to right; observations are accumulated newest-first.
def run_acc(-T: Data, ops: List<&2, E.Op<T>>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(T, rest, step_acc(T, op, st))

def finish(-T: Data, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, acc) = st
  (d, List.reverse(&2, E.Obs<T>, acc))

# Final state and the observation of every operation, in order.
def run(-T: Data, ops: List<&2, E.Op<T>>, d: Deque<T>) -> Deque<T> & List<&2, E.Obs<T>>:
  finish(T, run_acc(T, ops, (d, Nil{})))

# ---- executable specializations at a closed element type ----
#
# Bend 2.0.16's native C backend miscompiles Base.Array operations whose
# element type is still open (an erased `-T` parameter); see
# docs/VALIDATION.md, tests/runtime_defects/ and the same arrangement in
# src/dynamic_array.bend. The parametric definitions above are what the
# proofs are about; the `*_at` definitions below are template specializations
# (`~T` is a compile-time parameter, so every Base.Array call is compiled at a
# closed element type) and proofs/deque/closed.bend proves each of them equal
# to its parametric original, so every law transfers.

def empty_slots_at(~T: Data, +depth: Nat) -> Array<Maybe<&2, T>>:
  Array.new(Maybe<&2, T>, depth, None{})

def new_at(~T: Data) -> Deque<T>:
  DQ{0n, 1n, 0n, 0n, empty_slots_at(~T, 0n)}

def grown_back_at(~T: Data, +depth: Nat, a: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{a, empty_slots_at(~T, depth)}

def grown_front_at(~T: Data, +depth: Nat, a: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{empty_slots_at(~T, depth), a}

def pb_room_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, +len: Nat, a: Array<Maybe<&2, T>>, v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      DQ{dep, cp, lo, 1n+len, Array.set(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, len)), Some{v})}
    case False{}:
      DQ{1n+dep, Nat.double(cp), lo, 1n+len, Array.set(Maybe<&2, T>, grown_back_at(~T, dep, a), U32.from_nat(Nat.add(lo, len)), Some{v})}

def push_back_at(~T: Data, d: Deque<T>, v: T) -> Deque<T>:
  DQ{+dep, +cp, +lo, +len, a} = d
  pb_room_at(~T, dep, cp, lo, len, a, v, Nat.is_lt(Nat.add(lo, len), cp))

def pf_lo_at(~T: Data, +dep: Nat, +cp: Nat, lo: Nat, +len: Nat, a: Array<Maybe<&2, T>>, v: T) -> Deque<T>:
  match lo:
    case 0n:
      DQ{1n+dep, Nat.double(cp), dec1(cp), 1n+len, Array.set(Maybe<&2, T>, grown_front_at(~T, dep, a), U32.from_nat(dec1(cp)), Some{v})}
    case 1n+ +k:
      DQ{dep, cp, k, 1n+len, Array.set(Maybe<&2, T>, a, U32.from_nat(k), Some{v})}

def push_front_at(~T: Data, d: Deque<T>, v: T) -> Deque<T>:
  DQ{+dep, +cp, lo, +len, a} = d
  pf_lo_at(~T, dep, cp, lo, len, a, v)

def pop_f_len_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      pop_f_fin(T, dep, cp, lo, m, Array.swap(Maybe<&2, T>, a, U32.from_nat(lo), None{}))

def pop_front_at(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  pop_f_len_at(~T, dep, cp, lo, len, a)

def pop_b_len_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      pop_b_fin(T, dep, cp, lo, m, Array.swap(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m)), None{}))

def pop_back_at(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  pop_b_len_at(~T, dep, cp, lo, len, a)

def peek_f_len_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(T, dep, cp, lo, 1n+m, Array.get(Maybe<&2, T>, a, U32.from_nat(lo)))

def peek_front_at(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  peek_f_len_at(~T, dep, cp, lo, len, a)

def peek_b_len_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(T, dep, cp, lo, 1n+m, Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m))))

def peek_back_at(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  peek_b_len_at(~T, dep, cp, lo, len, a)

def tl_go_at(~T: Data, k: Nat, +lo: Nat, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & List<&2, T>:
  match k r:
    case 0n Tuple{a, x}:
      (a, acc)
    case 1n+ +m Tuple{a, x}:
      tl_go_at(~T, m, lo, cons_mb(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, dec1(m)))))

def tl_start_at(~T: Data, +dep: Nat, +cp: Nat, +lo: Nat, len: Nat, a: Array<Maybe<&2, T>>) -> Deque<T> & List<&2, T>:
  match len:
    case 0n:
      (DQ{dep, cp, lo, 0n, a}, Nil{})
    case 1n+ +m:
      tl_done(T, dep, cp, lo, 1n+m, tl_go_at(~T, 1n+m, lo, Nil{}, Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, m)))))

def to_list_at(~T: Data, d: Deque<T>) -> Deque<T> & List<&2, T>:
  DQ{+dep, +cp, +lo, len, a} = d
  tl_start_at(~T, dep, cp, lo, len, a)

def step_at(~T: Data, d: Deque<T>, op: E.Op<T>) -> Deque<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(T, length(T, d))
    case E.PushFront{x}:
      (push_front_at(~T, d, x), E.OUnit{})
    case E.PushBack{x}:
      (push_back_at(~T, d, x), E.OUnit{})
    case E.PopFront{}:
      obs_item(T, pop_front_at(~T, d))
    case E.PopBack{}:
      obs_item(T, pop_back_at(~T, d))
    case E.PeekFront{}:
      obs_item(T, peek_front_at(~T, d))
    case E.PeekBack{}:
      obs_item(T, peek_back_at(~T, d))
    case E.ToList{}:
      obs_list(T, to_list_at(~T, d))

def step_acc_at(~T: Data, op: E.Op<T>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  (d, acc) = st
  record(T, acc, step_at(~T, d, op))

def run_acc_at(~T: Data, ops: List<&2, E.Op<T>>, st: Deque<T> & List<&2, E.Obs<T>>) -> Deque<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc_at(~T, rest, step_acc_at(~T, op, st))

def run_at(~T: Data, ops: List<&2, E.Op<T>>, d: Deque<T>) -> Deque<T> & List<&2, E.Obs<T>>:
  finish(T, run_acc_at(~T, ops, (d, Nil{})))
