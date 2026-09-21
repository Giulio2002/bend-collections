import Base
import ./pow2.bend as P2
import ../types/dynamic_array.bend as E

# Growable, bounds-checked array over native Base.Array.
#
# Representation: DA{limit, depth, cap, length, slots} with cap = 2^depth kept
# in the record (recomputing 2^depth per operation would make every push,
# capacity and reserve cost O(depth)). `slots` is a Base.Array of
# 2^depth slots. ALeaf/ANode is the LOGICAL model the checker reasons about;
# stock Bend 2.0.16 lowers a Base.Array to one indexed memory block, and
# get/set/swap compile to a `blk_at` index computation plus a direct
# `blk_read`/`blk_write` (docs/C_EQUIVALENCE.md). Slots [0, length)
# hold Some{x}; the rest hold None. Capacity is 2^depth. `limit` (<= 31) caps
# depth, so every capacity is representable as the U32 size Base computes, and
# every index passed to Base is < 2^depth <= 2^31 (so Base's masking is the
# identity). Out-of-range indices never reach Base.
#
# Errors return the state unchanged (see docs/API.md):
#   get/set out of range -> IndexOutOfRange; pop on empty -> EmptyArray;
#   push/reserve beyond 2^limit -> CapacityExceeded.
# Cost (n = length, c = capacity): get/set/push/pop are one indexed load or
# store into the block (no tree descent in the native lowering), growth O(c)
# (a fresh half is allocated and the merged block copied, like a C realloc),
# reserve O(target capacity), clear O(c), to_list O(c).

type DynArray<-T: Data> is Type:
  DA{limit: Nat, depth: Nat, cap: Nat, length: Nat, slots: Array<Maybe<&2, T>>}

def max_depth() -> Nat:
  31n

# 2^d (structural doubling; Base Nat.pow is avoided, see docs/VALIDATION.md).
def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

def empty_slots(-T: Data, +depth: Nat) -> Array<Maybe<&2, T>>:
  Array.new(Maybe<&2, T>, depth, None{})

def new(-T: Data) -> DynArray<T>:
  DA{max_depth(), 0n, 1n, 0n, empty_slots(T, 0n)}

# Depth limit min(k, 31). (Written with an explicit match: Base Nat.min is a
# Bool.pick over shared arguments, which miscompiled at runtime; docs/VALIDATION.md.)
def clamp_limit(k: Nat, small: Bool) -> Nat:
  match small:
    case True{}:
      k
    case False{}:
      max_depth()

# Same as new, with capacity bounded by 2^min(k, 31).
def with_limit(-T: Data, +k: Nat) -> DynArray<T>:
  DA{clamp_limit(k, Nat.is_lt(k, max_depth())), 0n, 1n, 0n, empty_slots(T, 0n)}

def length(-T: Data, da: DynArray<T>) -> DynArray<T> & Nat:
  DA{limit, depth, cap, +len, arr} = da
  (DA{limit, depth, cap, len, arr}, len)

def capacity(-T: Data, da: DynArray<T>) -> DynArray<T> & Nat:
  DA{limit, depth, +cap, len, arr} = da
  (DA{limit, depth, cap, len, arr}, cap)

def slot_result(-T: Data, slot: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match slot:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{x}:
      Done{x}

# ---- get ----

def get_found(-T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  (arr, slot) = r
  (DA{limit, depth, cap, len, arr}, slot_result(T, slot))

def get_checked(-T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, i: Nat, ok: Bool) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  match ok:
    case True{}:
      get_found(T, limit, depth, cap, len, Array.get(Maybe<&2, T>, arr, U32.from_nat(i)))
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.IndexOutOfRange{}})

def get(-T: Data, da: DynArray<T>, +i: Nat) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  DA{limit, depth, cap, +len, arr} = da
  get_checked(T, limit, depth, cap, len, arr, i, Nat.is_lt(i, len))

# ---- set ----

def set_checked(-T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, i: Nat, v: T, ok: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      (DA{limit, depth, cap, len, Array.set(Maybe<&2, T>, arr, U32.from_nat(i), Some{v})}, Done{Unit{}})
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.IndexOutOfRange{}})

def set(-T: Data, da: DynArray<T>, +i: Nat, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{limit, depth, cap, +len, arr} = da
  set_checked(T, limit, depth, cap, len, arr, i, v, Nat.is_lt(i, len))

# ---- growth ----

# Doubling: the old tree becomes the left half of a tree one level deeper.
def grown(-T: Data, +depth: Nat, arr: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{arr, empty_slots(T, depth)}

def push_room(-T: Data, limit: Nat, +depth: Nat, +cap: Nat, +len: Nat, arr: Array<Maybe<&2, T>>, v: T, room: Bool, grow: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match room grow:
    case True{} _:
      (DA{limit, depth, cap, 1n+len, Array.set(Maybe<&2, T>, arr, U32.from_nat(len), Some{v})}, Done{Unit{}})
    case False{} True{}:
      (DA{limit, 1n+depth, Nat.double(cap), 1n+len, Array.set(Maybe<&2, T>, grown(T, depth, arr), U32.from_nat(len), Some{v})}, Done{Unit{}})
    case False{} False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.CapacityExceeded{}})

def push(-T: Data, da: DynArray<T>, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{+limit, +depth, +cap, +len, arr} = da
  push_room(T, limit, depth, cap, len, arr, v, Nat.is_lt(len, cap), Nat.is_lt(depth, limit))

# ---- pop ----

def pop_found(-T: Data, limit: Nat, depth: Nat, +cap: Nat, m: Nat, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  (arr, old) = r
  (DA{limit, depth, cap, m, arr}, slot_result(T, old))

def pop_len(-T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DA{limit, depth, cap, 0n, arr}, Fail{E.EmptyArray{}})
    case 1n+ +m:
      pop_found(T, limit, depth, cap, m, Array.swap(Maybe<&2, T>, arr, U32.from_nat(m), None{}))

def pop(-T: Data, da: DynArray<T>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  DA{limit, depth, cap, len, arr} = da
  pop_len(T, limit, depth, cap, len, arr)

# ---- reserve ----

def grow_if(-T: Data, limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, fits: Bool) -> DynArray<T>:
  match fits:
    case True{}:
      DA{limit, depth, cap, len, arr}
    case False{}:
      DA{limit, 1n+depth, Nat.double(cap), len, grown(T, depth, arr)}

def grow_step(-T: Data, +n: Nat, st: DynArray<T>) -> DynArray<T>:
  DA{limit, +depth, +cap, len, arr} = st
  grow_if(T, limit, depth, cap, len, arr, Nat.is_le(n, cap))

# Doubles until n fits; `fuel` = limit - depth bounds the number of doublings.
def grow_until(-T: Data, fuel: Nat, +n: Nat, st: DynArray<T>) -> DynArray<T>:
  match fuel:
    case 0n:
      st
    case 1n+f:
      grow_until(T, f, n, grow_step(T, n, st))

# The feasibility test (n <= 2^limit) is only reached when the cached capacity
# does not already suffice: computing 2^limit is O(limit) and reserve is
# otherwise O(1).
def reserve_room(-T: Data, +limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, +n: Nat, feasible: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match feasible:
    case True{}:
      (grow_until(T, Nat.sub(limit, depth), n, DA{limit, depth, cap, len, arr}), Done{Unit{}})
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.CapacityExceeded{}})

def reserve_checked(-T: Data, +limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, +n: Nat, fits: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match fits:
    case True{}:
      (DA{limit, depth, cap, len, arr}, Done{Unit{}})
    case False{}:
      reserve_room(T, limit, depth, cap, len, arr, n, Nat.is_le(n, pow2(limit)))

# Ensures capacity >= n (new capacity: least 2^k >= n with k >= depth).
def reserve(-T: Data, da: DynArray<T>, +n: Nat) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{+limit, +depth, +cap, len, arr} = da
  reserve_checked(T, limit, depth, cap, len, arr, n, Nat.is_le(n, cap))

# ---- clear / to_list ----

# Keeps the capacity; all slots become None.
def clear(-T: Data, da: DynArray<T>) -> DynArray<T>:
  DA{limit, +depth, +cap, len, arr} = da
  DA{limit, depth, cap, 0n, empty_slots(T, depth)}

# to_list walks the occupied slots BY INDEX, newest first, and conses them:
# the walk gives the array back, so nothing is cloned, and a `Base.Array` is
# never matched structurally (that destroys the flat representation, see
# docs/VALIDATION.md).
def cons_some(-T: Data, x: Maybe<&2, T>, acc: List<&2, T>) -> List<&2, T>:
  match x:
    case None{}:
      acc
    case Some{v}:
      Con{v, acc}

def dec1(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# k slots are still to be read, the last of them first: the pair `r` is slot
# k - 1, already read.
def tl_go(k: Nat, -T: Data, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & List<&2, T>:
  match k r:
    case 0n Tuple{a, x}:
      (a, acc)
    case 1n+ +m Tuple{a, x}:
      tl_go(m, T, cons_some(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(dec1(m))))

def tl_done(-T: Data, limit: Nat, depth: Nat, +cap: Nat, +len: Nat, r: Array<Maybe<&2, T>> & List<&2, T>) -> DynArray<T> & List<&2, T>:
  (a, xs) = r
  (DA{limit, depth, cap, len, a}, xs)

def tl_start(-T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>) -> DynArray<T> & List<&2, T>:
  match len:
    case 0n:
      (DA{limit, depth, cap, 0n, arr}, Nil{})
    case 1n+ +m:
      tl_done(T, limit, depth, cap, 1n+m, tl_go(1n+m, T, Nil{}, Array.get(Maybe<&2, T>, arr, U32.from_nat(m))))

def to_list(-T: Data, da: DynArray<T>) -> DynArray<T> & List<&2, T>:
  DA{limit, depth, +cap, len, arr} = da
  tl_start(T, limit, depth, cap, len, arr)

# ---- operation traces ----

def obs_nat(-T: Data, r: DynArray<T> & Nat) -> DynArray<T> & E.Obs<T>:
  (d, n) = r
  (d, E.ONat{n})

def obs_item(-T: Data, r: DynArray<T> & Result<&2, &2, E.Error, T>) -> DynArray<T> & E.Obs<T>:
  (d, x) = r
  (d, E.OItem{x})

def obs_unit(-T: Data, r: DynArray<T> & Result<&2, &2, E.Error, Unit>) -> DynArray<T> & E.Obs<T>:
  (d, x) = r
  (d, E.OUnit{x})

def obs_list(-T: Data, r: DynArray<T> & List<&2, T>) -> DynArray<T> & E.Obs<T>:
  (d, xs) = r
  (d, E.OList{xs})

def step(-T: Data, da: DynArray<T>, op: E.Op<T>) -> DynArray<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(T, length(T, da))
    case E.Capacity{}:
      obs_nat(T, capacity(T, da))
    case E.Get{i}:
      obs_item(T, get(T, da, i))
    case E.Set{i, v}:
      obs_unit(T, set(T, da, i, v))
    case E.Push{v}:
      obs_unit(T, push(T, da, v))
    case E.Pop{}:
      obs_item(T, pop(T, da))
    case E.Reserve{n}:
      obs_unit(T, reserve(T, da, n))
    case E.Clear{}:
      (clear(T, da), E.OUnit{Done{Unit{}}})
    case E.ToList{}:
      obs_list(T, to_list(T, da))

def record(-T: Data, acc: List<&2, E.Obs<T>>, r: DynArray<T> & E.Obs<T>) -> DynArray<T> & List<&2, E.Obs<T>>:
  (da, o) = r
  (da, Con{o, acc})

def step_acc(-T: Data, op: E.Op<T>, st: DynArray<T> & List<&2, E.Obs<T>>) -> DynArray<T> & List<&2, E.Obs<T>>:
  (da, acc) = st
  record(T, acc, step(T, da, op))

# Runs ops left to right; observations are accumulated newest-first.
def run_acc(-T: Data, ops: List<&2, E.Op<T>>, st: DynArray<T> & List<&2, E.Obs<T>>) -> DynArray<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(T, rest, step_acc(T, op, st))

def finish(-T: Data, st: DynArray<T> & List<&2, E.Obs<T>>) -> DynArray<T> & List<&2, E.Obs<T>>:
  (da, acc) = st
  (da, List.reverse(&2, E.Obs<T>, acc))

# Final state and the observation of every operation, in order.
def run(-T: Data, ops: List<&2, E.Op<T>>, da: DynArray<T>) -> DynArray<T> & List<&2, E.Obs<T>>:
  finish(T, run_acc(T, ops, (da, Nil{})))

# ---- executable specializations at a closed element type ----
#
# Bend 2.0.16's native C backend miscompiles Base.Array operations whose
# element type is still open (an erased `-T` parameter): `Array.new` at a bare
# type variable is rejected outright ("an open Array element type"), and
# `Array.get`/`Array.set`/`Array.swap`/`Array.clone` under `Maybe<&2, T>`
# silently read back wrong data for any element that is not a machine
# immediate. See docs/VALIDATION.md and tests/runtime_defects/.
#
# The definitions above stay parametric, so their proofs are universal in T.
# The `*_at` definitions below are template specializations: `~T` is a
# compile-time parameter, so every Base.Array call is compiled at a closed
# element type. They are the entry points used by tests and benchmarks, and
# proofs/dynamic_array/closed.bend proves each of them equal to the
# parametric definition at its instance, so every law above transfers.
#
# Only the definitions that (transitively) reach a Base.Array call need a
# specialization; the purely structural helpers are shared.

def empty_slots_at(~T: Data, +depth: Nat) -> Array<Maybe<&2, T>>:
  Array.new(Maybe<&2, T>, depth, None{})

def new_at(~T: Data) -> DynArray<T>:
  DA{max_depth(), 0n, 1n, 0n, empty_slots_at(~T, 0n)}

def with_limit_at(~T: Data, +k: Nat) -> DynArray<T>:
  DA{clamp_limit(k, Nat.is_lt(k, max_depth())), 0n, 1n, 0n, empty_slots_at(~T, 0n)}

def get_checked_at(~T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, i: Nat, ok: Bool) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  match ok:
    case True{}:
      get_found(T, limit, depth, cap, len, Array.get(Maybe<&2, T>, arr, U32.from_nat(i)))
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.IndexOutOfRange{}})

def get_at(~T: Data, da: DynArray<T>, +i: Nat) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  DA{limit, depth, cap, +len, arr} = da
  get_checked_at(~T, limit, depth, cap, len, arr, i, Nat.is_lt(i, len))

def set_checked_at(~T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, i: Nat, v: T, ok: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      (DA{limit, depth, cap, len, Array.set(Maybe<&2, T>, arr, U32.from_nat(i), Some{v})}, Done{Unit{}})
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.IndexOutOfRange{}})

def set_at(~T: Data, da: DynArray<T>, +i: Nat, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{limit, depth, cap, +len, arr} = da
  set_checked_at(~T, limit, depth, cap, len, arr, i, v, Nat.is_lt(i, len))

def grown_at(~T: Data, +depth: Nat, arr: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{arr, empty_slots_at(~T, depth)}

def push_room_at(~T: Data, limit: Nat, +depth: Nat, +cap: Nat, +len: Nat, arr: Array<Maybe<&2, T>>, v: T, room: Bool, grow: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match room grow:
    case True{} _:
      (DA{limit, depth, cap, 1n+len, Array.set(Maybe<&2, T>, arr, U32.from_nat(len), Some{v})}, Done{Unit{}})
    case False{} True{}:
      (DA{limit, 1n+depth, Nat.double(cap), 1n+len, Array.set(Maybe<&2, T>, grown_at(~T, depth, arr), U32.from_nat(len), Some{v})}, Done{Unit{}})
    case False{} False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.CapacityExceeded{}})

def push_at(~T: Data, da: DynArray<T>, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{+limit, +depth, +cap, +len, arr} = da
  push_room_at(~T, limit, depth, cap, len, arr, v, Nat.is_lt(len, cap), Nat.is_lt(depth, limit))

def pop_len_at(~T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DA{limit, depth, cap, 0n, arr}, Fail{E.EmptyArray{}})
    case 1n+ +m:
      pop_found(T, limit, depth, cap, m, Array.swap(Maybe<&2, T>, arr, U32.from_nat(m), None{}))

def pop_at(~T: Data, da: DynArray<T>) -> DynArray<T> & Result<&2, &2, E.Error, T>:
  DA{limit, depth, cap, len, arr} = da
  pop_len_at(~T, limit, depth, cap, len, arr)

def grow_if_at(~T: Data, limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, fits: Bool) -> DynArray<T>:
  match fits:
    case True{}:
      DA{limit, depth, cap, len, arr}
    case False{}:
      DA{limit, 1n+depth, Nat.double(cap), len, grown_at(~T, depth, arr)}

def grow_step_at(~T: Data, +n: Nat, st: DynArray<T>) -> DynArray<T>:
  DA{limit, +depth, +cap, len, arr} = st
  grow_if_at(~T, limit, depth, cap, len, arr, Nat.is_le(n, cap))

def grow_until_at(~T: Data, fuel: Nat, +n: Nat, st: DynArray<T>) -> DynArray<T>:
  match fuel:
    case 0n:
      st
    case 1n+f:
      grow_until_at(~T, f, n, grow_step_at(~T, n, st))

# The feasibility test (n <= 2^limit) is only reached when the cached capacity
# does not already suffice: computing 2^limit is O(limit) and reserve is
# otherwise O(1).
def reserve_room_at(~T: Data, +limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, +n: Nat, feasible: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match feasible:
    case True{}:
      (grow_until_at(~T, Nat.sub(limit, depth), n, DA{limit, depth, cap, len, arr}), Done{Unit{}})
    case False{}:
      (DA{limit, depth, cap, len, arr}, Fail{E.CapacityExceeded{}})

def reserve_checked_at(~T: Data, +limit: Nat, +depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>, +n: Nat, fits: Bool) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  match fits:
    case True{}:
      (DA{limit, depth, cap, len, arr}, Done{Unit{}})
    case False{}:
      reserve_room_at(~T, limit, depth, cap, len, arr, n, Nat.is_le(n, P2.pow2t(limit)))

def reserve_at(~T: Data, da: DynArray<T>, +n: Nat) -> DynArray<T> & Result<&2, &2, E.Error, Unit>:
  DA{+limit, +depth, +cap, len, arr} = da
  reserve_checked_at(~T, limit, depth, cap, len, arr, n, Nat.is_le(n, cap))

# The executable clear allocates the fresh all-None block, exactly as the
# parametric `clear` does and exactly as benchmarks/native/dynamic_array.c
# rewrites the slots: the capacity is kept and every slot is empty again.
# (An "already empty, keep the block" fast path was tried in iteration 0011
# and removed in 0013: it only pays off when a benchmark clears the same
# empty array over and over, and it made the clear rows unmeasurable because
# the calibration then compares a no-op against the reference's real work.)
def clear_at(~T: Data, da: DynArray<T>) -> DynArray<T>:
  DA{+limit, +depth, +cap, len, arr} = da
  DA{limit, depth, cap, 0n, empty_slots_at(~T, depth)}

# The executable to_list is the same indexed walk, compiled at a closed
# element type; proofs/dynamic_array/closed.bend proves the two agree.
def tl_go_at(~T: Data, k: Nat, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & List<&2, T>:
  match k r:
    case 0n Tuple{a, x}:
      (a, acc)
    case 1n+ +m Tuple{a, x}:
      tl_go_at(~T, m, cons_some(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(dec1(m))))

def tl_start_at(~T: Data, limit: Nat, depth: Nat, +cap: Nat, len: Nat, arr: Array<Maybe<&2, T>>) -> DynArray<T> & List<&2, T>:
  match len:
    case 0n:
      (DA{limit, depth, cap, 0n, arr}, Nil{})
    case 1n+ +m:
      tl_done(T, limit, depth, cap, 1n+m, tl_go_at(~T, 1n+m, Nil{}, Array.get(Maybe<&2, T>, arr, U32.from_nat(m))))

def to_list_at(~T: Data, da: DynArray<T>) -> DynArray<T> & List<&2, T>:
  DA{limit, depth, +cap, len, arr} = da
  tl_start_at(~T, limit, depth, cap, len, arr)

def step_at(~T: Data, da: DynArray<T>, op: E.Op<T>) -> DynArray<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(T, length(T, da))
    case E.Capacity{}:
      obs_nat(T, capacity(T, da))
    case E.Get{i}:
      obs_item(T, get_at(~T, da, i))
    case E.Set{i, v}:
      obs_unit(T, set_at(~T, da, i, v))
    case E.Push{v}:
      obs_unit(T, push_at(~T, da, v))
    case E.Pop{}:
      obs_item(T, pop_at(~T, da))
    case E.Reserve{n}:
      obs_unit(T, reserve_at(~T, da, n))
    case E.Clear{}:
      (clear_at(~T, da), E.OUnit{Done{Unit{}}})
    case E.ToList{}:
      obs_list(T, to_list_at(~T, da))

def step_acc_at(~T: Data, op: E.Op<T>, st: DynArray<T> & List<&2, E.Obs<T>>) -> DynArray<T> & List<&2, E.Obs<T>>:
  (da, acc) = st
  record(T, acc, step_at(~T, da, op))

def run_acc_at(~T: Data, ops: List<&2, E.Op<T>>, st: DynArray<T> & List<&2, E.Obs<T>>) -> DynArray<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc_at(~T, rest, step_acc_at(~T, op, st))

def run_at(~T: Data, ops: List<&2, E.Op<T>>, da: DynArray<T>) -> DynArray<T> & List<&2, E.Obs<T>>:
  finish(T, run_acc_at(~T, ops, (da, Nil{})))
