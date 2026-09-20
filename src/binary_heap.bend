import Base
import ../types/binary_heap.bend as E

# Min-heap in a PACKED native array: the elements live in slots [0, size) of a
# `Base.Array` of 2^depth slots, element i having children 2i+1 and 2i+2 and
# parent (i-1)/2. No node is allocated per element and no link is stored: the
# heap shape is the index arithmetic (docs/ARCHITECTURE.md).
#
#   push   writes the element at slot `size` and SIFTS IT UP while its parent
#          is larger (early exit: the loop stops at the first parent that is
#          not larger, which is what makes a random push O(1) on average),
#   pop    takes slot 0, moves the last element to the root and SIFTS IT DOWN
#          through the smaller child,
#   peek   reads slot 0, length is the cached size,
#   to_sorted_list clones the array and drains the clone (the heap itself is
#          returned unchanged),
#   from_list is repeated push.
#
# Index arithmetic uses `U32.shl` (doubling), `U32.inc` (+1) and `U32.shr`
# (halving) rather than `U32.add`, because those are exactly the operations
# whose Nat meaning the proofs can bridge without ever naming 2^32 -- a
# literal the checker would have to expand as a unary Nat
# (proofs/binary_heap/u32idx.bend).
#
# The record caches what would otherwise be recomputed per operation: `n` is
# the size as a U32 (the index the next push writes), `cap` = 2^depth as a
# U32, and `depth` bounds every sift loop. Indices are U32 throughout, so no
# index arithmetic walks a unary Nat; `size` stays a Nat because that is what
# the specification's `length` is.
#
# The order is a static comparator ~cmp : A -> A -> Cmp (a template
# parameter); its total-order laws are proof obligations of each instance
# (proofs/lib/order.bend: U32 and String). Elements equal under cmp are
# identical under the laws, so multiplicities are exact.
#
# Cost (n = size): push O(log n) worst case and O(1) expected, pop O(log n),
# peek/length O(1), from_list O(n log n), to_sorted_list O(n log n) plus one
# O(n) array clone. Capacity doubles when a push finds the block full; depth
# is bounded by 31, so every slot index is a representable U32.
# Errors: peek/pop on an empty heap -> Fail{EmptyHeap}, heap unchanged.

type Heap<-A: Data> is Type:
  BH{size: Nat, n: U32, depth: Nat, cap: U32, slots: Array<Maybe<&2, A>>}

def max_depth() -> Nat:
  31n

def le(~A: Data, ~cmp: A -> A -> Cmp, x: A, y: A) -> Bool:
  Cmp.is_le(cmp(x, y))

def empty_slots(~A: Data, +depth: Nat) -> Array<Maybe<&2, A>>:
  Array.new(Maybe<&2, A>, depth, None{})

def new(~A: Data) -> Heap<A>:
  BH{0n, 0, 0n, 1, empty_slots(~A, 0n)}

def length(~A: Data, h: Heap<A>) -> Heap<A> & Nat:
  BH{+size, n, depth, cap, arr} = h
  (BH{size, n, depth, cap, arr}, size)

# ---- reading a slot ----

# The slot value, with a default that a well-formed heap never needs (every
# index a sift loop reads is inside [0, size), where the slot is Some).
def slot_or(~A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def item_of(~A: Data, m: Maybe<&2, A>) -> Result<&2, &2, E.Error, A>:
  match m:
    case None{}:
      Fail{E.EmptyHeap{}}
    case Some{v}:
      Done{v}

# ---- sift up ----
#
# A sift loop cannot be written as one recursive function with an early exit
# in Bend: `match` only scrutinises a parameter, and definitions may not be
# mutually recursive. The loop therefore carries its decision in a state that
# an earlier (non-recursive) probe builds: `UStop{arr, i}` means the sifted
# value belongs at slot i, `UMove{arr, i, pv, p}` means the parent value pv
# moves down into slot i and the sift goes on at p.

type Up<-A: Data> is Type:
  UStop{arr: Array<Maybe<&2, A>>, i: U32}
  UMove{arr: Array<Maybe<&2, A>>, i: U32, pv: A, p: U32}

# The parent index of i (i > 0). For i = 0 the probe never reads it.
def parent(+i: U32) -> U32:
  U32.shr(U32.sub(i, 1))

def up_dec(~A: Data, arr: Array<Maybe<&2, A>>, i: U32, pv: A, p: U32, ok: Bool) -> Up<A>:
  match ok:
    case True{}:
      UStop{arr, i}
    case False{}:
      UMove{arr, i, pv, p}

def up_mb(~A: Data, ~cmp: A -> A -> Cmp, arr: Array<Maybe<&2, A>>, i: U32, +x: A, p: U32, m: Maybe<&2, A>) -> Up<A>:
  match m:
    case None{}:
      UStop{arr, i}
    case Some{+pv}:
      up_dec(~A, arr, i, pv, p, le(~A, ~cmp, pv, x))

def up_slot(~A: Data, ~cmp: A -> A -> Cmp, i: U32, x: A, p: U32, r: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Up<A>:
  (arr, m) = r
  up_mb(~A, ~cmp, arr, i, x, p, m)

def up_root(~A: Data, ~cmp: A -> A -> Cmp, +i: U32, x: A, arr: Array<Maybe<&2, A>>, root: Bool) -> Up<A>:
  match root:
    case True{}:
      UStop{arr, i}
    case False{}:
      up_slot(~A, ~cmp, i, x, parent(i), Array.get(Maybe<&2, A>, arr, parent(i)))

# Where the value x, currently destined for slot i, must go next.
def up_probe(~A: Data, ~cmp: A -> A -> Cmp, +i: U32, +x: A, arr: Array<Maybe<&2, A>>) -> Up<A>:
  up_root(~A, ~cmp, i, x, arr, U32.is_eq(i, 0))

def up_go(~A: Data, ~cmp: A -> A -> Cmp, fuel: Nat, +x: A, st: Up<A>) -> Array<Maybe<&2, A>>:
  match fuel st:
    case 0n UStop{arr, i}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 0n UMove{arr, i, pv, p}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 1n+f UStop{arr, i}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 1n+f UMove{arr, i, +pv, +p}:
      up_go(~A, ~cmp, f, x, up_probe(~A, ~cmp, p, x, Array.set(Maybe<&2, A>, arr, i, Some{pv})))

# Place x at slot i and restore heap order upwards (fuel bounds the climb).
def sift_up(~A: Data, ~cmp: A -> A -> Cmp, fuel: Nat, i: U32, +x: A, arr: Array<Maybe<&2, A>>) -> Array<Maybe<&2, A>>:
  up_go(~A, ~cmp, fuel, x, up_probe(~A, ~cmp, i, x, arr))

# ---- sift down ----

type Down<-A: Data> is Type:
  DStop{arr: Array<Maybe<&2, A>>, i: U32}
  DMove{arr: Array<Maybe<&2, A>>, i: U32, cv: A, ci: U32}

def down_dec(~A: Data, arr: Array<Maybe<&2, A>>, i: U32, cv: A, ci: U32, ok: Bool) -> Down<A>:
  match ok:
    case True{}:
      DStop{arr, i}
    case False{}:
      DMove{arr, i, cv, ci}

def down_two(~A: Data, ~cmp: A -> A -> Cmp, arr: Array<Maybe<&2, A>>, i: U32, +x: A, l: U32, +lv: A, r: U32, +rv: A, left: Bool) -> Down<A>:
  match left:
    case True{}:
      down_dec(~A, arr, i, lv, l, le(~A, ~cmp, x, lv))
    case False{}:
      down_dec(~A, arr, i, rv, r, le(~A, ~cmp, x, rv))

def down_rmb(~A: Data, ~cmp: A -> A -> Cmp, arr: Array<Maybe<&2, A>>, i: U32, +x: A, l: U32, +lv: A, r: U32, m: Maybe<&2, A>) -> Down<A>:
  match m:
    case None{}:
      down_dec(~A, arr, i, lv, l, le(~A, ~cmp, x, lv))
    case Some{+rv}:
      down_two(~A, ~cmp, arr, i, x, l, lv, r, rv, le(~A, ~cmp, lv, rv))

def down_rslot(~A: Data, ~cmp: A -> A -> Cmp, i: U32, x: A, l: U32, +lv: A, r: U32, rr: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Down<A>:
  (arr, m) = rr
  down_rmb(~A, ~cmp, arr, i, x, l, lv, r, m)

def down_lmb(~A: Data, ~cmp: A -> A -> Cmp, arr: Array<Maybe<&2, A>>, i: U32, +x: A, +l: U32, two: Bool, m: Maybe<&2, A>) -> Down<A>:
  match two m:
    case _ None{}:
      DStop{arr, i}
    case True{} Some{+lv}:
      down_rslot(~A, ~cmp, i, x, l, lv, U32.inc(l), Array.get(Maybe<&2, A>, arr, U32.inc(l)))
    case False{} Some{+lv}:
      down_dec(~A, arr, i, lv, l, le(~A, ~cmp, x, lv))

def down_lslot(~A: Data, ~cmp: A -> A -> Cmp, i: U32, +x: A, +l: U32, two: Bool, r: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Down<A>:
  (arr, m) = r
  down_lmb(~A, ~cmp, arr, i, x, l, two, m)

def down_has(~A: Data, ~cmp: A -> A -> Cmp, +size: U32, i: U32, x: A, arr: Array<Maybe<&2, A>>, +l: U32, has_left: Bool) -> Down<A>:
  match has_left:
    case True{}:
      down_lslot(~A, ~cmp, i, x, l, U32.is_lt(l, U32.sub(size, 1)), Array.get(Maybe<&2, A>, arr, l))
    case False{}:
      DStop{arr, i}

# Where the value x, currently destined for slot i of a heap of `size`
# elements, must go next.
def down_probe(~A: Data, ~cmp: A -> A -> Cmp, +size: U32, +i: U32, x: A, arr: Array<Maybe<&2, A>>) -> Down<A>:
  down_has(~A, ~cmp, size, i, x, arr, U32.inc(U32.shl(i)), U32.is_lt(U32.inc(U32.shl(i)), size))

def down_go(~A: Data, ~cmp: A -> A -> Cmp, fuel: Nat, +size: U32, +x: A, st: Down<A>) -> Array<Maybe<&2, A>>:
  match fuel st:
    case 0n DStop{arr, i}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 0n DMove{arr, i, cv, ci}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 1n+f DStop{arr, i}:
      Array.set(Maybe<&2, A>, arr, i, Some{x})
    case 1n+f DMove{arr, i, +cv, +ci}:
      down_go(~A, ~cmp, f, size, x, down_probe(~A, ~cmp, size, ci, x, Array.set(Maybe<&2, A>, arr, i, Some{cv})))

# Place x at slot i of a heap of `size` elements and restore heap order down.
def sift_down(~A: Data, ~cmp: A -> A -> Cmp, fuel: Nat, +size: U32, i: U32, +x: A, arr: Array<Maybe<&2, A>>) -> Array<Maybe<&2, A>>:
  down_go(~A, ~cmp, fuel, size, x, down_probe(~A, ~cmp, size, i, x, arr))

# ---- push ----

# Doubling: the old block becomes the lower half of a block one level deeper,
# so every element keeps its index.
def grown(~A: Data, +depth: Nat, arr: Array<Maybe<&2, A>>) -> Array<Maybe<&2, A>>:
  ANode{arr, empty_slots(~A, depth)}

def push_room(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +n: U32, +depth: Nat, +cap: U32, arr: Array<Maybe<&2, A>>, x: A, room: Bool) -> Heap<A>:
  match room:
    case True{}:
      BH{1n+size, U32.inc(n), depth, cap, sift_up(~A, ~cmp, depth, n, x, arr)}
    case False{}:
      BH{1n+size, U32.inc(n), 1n+depth, U32.shl(cap), sift_up(~A, ~cmp, 1n+depth, n, x, grown(~A, depth, arr))}

def push(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>, x: A) -> Heap<A>:
  BH{size, +n, +depth, +cap, arr} = h
  push_room(~A, ~cmp, size, n, depth, cap, arr, x, U32.is_lt(n, cap))

# ---- peek ----

def peek_found(~A: Data, size: Nat, n: U32, depth: Nat, cap: U32, r: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  (arr, m) = r
  (BH{size, n, depth, cap, arr}, item_of(~A, m))

def peek_go(~A: Data, size: Nat, +n: U32, depth: Nat, cap: U32, arr: Array<Maybe<&2, A>>, empty: Bool) -> Heap<A> & Result<&2, &2, E.Error, A>:
  match empty:
    case True{}:
      (BH{size, n, depth, cap, arr}, Fail{E.EmptyHeap{}})
    case False{}:
      peek_found(~A, size, n, depth, cap, Array.get(Maybe<&2, A>, arr, 0))

def peek(~A: Data, h: Heap<A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  BH{size, +n, depth, cap, arr} = h
  peek_go(~A, size, n, depth, cap, arr, U32.is_eq(n, 0))

# ---- pop ----

# The last element has been taken out of slot m = n - 1; put it at the root
# and sift it down over the remaining m elements.
def pop_move(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +m: U32, +depth: Nat, cap: U32, root: A, last: A, arr: Array<Maybe<&2, A>>, empty: Bool) -> Heap<A> & Result<&2, &2, E.Error, A>:
  match empty:
    case True{}:
      (BH{size, m, depth, cap, arr}, Done{root})
    case False{}:
      (BH{size, m, depth, cap, sift_down(~A, ~cmp, depth, m, 0, last, arr)}, Done{root})

def pop_last(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +m: U32, depth: Nat, cap: U32, +root: A, rl: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  (arr, ml) = rl
  pop_move(~A, ~cmp, size, m, depth, cap, root, slot_or(~A, root, ml), arr, U32.is_eq(m, 0))

# The root slot of a nonempty heap is Some; the None case cannot be reached
# from a well-formed heap and returns the state unchanged.
def pop_with(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +n: U32, depth: Nat, cap: U32, arr: Array<Maybe<&2, A>>, mr: Maybe<&2, A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  match mr:
    case None{}:
      (BH{size, n, depth, cap, arr}, Fail{E.EmptyHeap{}})
    case Some{+root}:
      pop_last(~A, ~cmp, Nat.sub(size, 1n), U32.sub(n, 1), depth, cap, root, Array.swap(Maybe<&2, A>, arr, U32.sub(n, 1), None{}))

def pop_root(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +n: U32, depth: Nat, cap: U32, rr: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  (arr, mr) = rr
  pop_with(~A, ~cmp, size, n, depth, cap, arr, mr)

def pop_go(~A: Data, ~cmp: A -> A -> Cmp, size: Nat, +n: U32, depth: Nat, cap: U32, arr: Array<Maybe<&2, A>>, empty: Bool) -> Heap<A> & Result<&2, &2, E.Error, A>:
  match empty:
    case True{}:
      (BH{size, n, depth, cap, arr}, Fail{E.EmptyHeap{}})
    case False{}:
      pop_root(~A, ~cmp, size, n, depth, cap, Array.get(Maybe<&2, A>, arr, 0))

def pop(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>) -> Heap<A> & Result<&2, &2, E.Error, A>:
  BH{size, +n, depth, cap, arr} = h
  pop_go(~A, ~cmp, size, n, depth, cap, arr, U32.is_eq(n, 0))

# ---- from_list ----

def from_list_go(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, h: Heap<A>) -> Heap<A>:
  match xs:
    case Nil{}:
      h
    case Con{x, rest}:
      from_list_go(~A, ~cmp, rest, push(~A, ~cmp, h, x))

def from_list(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Heap<A>:
  from_list_go(~A, ~cmp, xs, new(~A))

# ---- to_sorted_list ----

# Repeated root removal on a COPY of the block: the heap itself is unchanged.
# The loop carries its state for the same reason the sift loops do.
#   DrDone   the copy is exhausted
#   DrLast   the root was the last element
#   DrMore   the root is out, `m` elements remain and `last` has to sift down

type Drain<-A: Data> is Type:
  DrDone{arr: Array<Maybe<&2, A>>}
  DrLast{arr: Array<Maybe<&2, A>>, root: A}
  DrMore{arr: Array<Maybe<&2, A>>, root: A, m: U32, last: A}

# Dropping the (linear) block is O(1): the runtime erases it.
def burn(~A: Data, arr: Array<Maybe<&2, A>>) -> List<&2, A>:
  Nil{}

def burn_cons(~A: Data, root: A, arr: Array<Maybe<&2, A>>) -> List<&2, A>:
  Con{root, Nil{}}

def drain_mb(~A: Data, arr: Array<Maybe<&2, A>>, root: A, +m: U32, ml: Maybe<&2, A>, empty: Bool) -> Drain<A>:
  match ml empty:
    case None{} _:
      DrLast{arr, root}
    case Some{last} True{}:
      DrLast{arr, root}
    case Some{last} False{}:
      DrMore{arr, root, m, last}

def drain_last(~A: Data, root: A, +m: U32, empty: Bool, rl: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Drain<A>:
  (arr, ml) = rl
  drain_mb(~A, arr, root, m, ml, empty)

def drain_root(~A: Data, arr: Array<Maybe<&2, A>>, +m: U32, mr: Maybe<&2, A>) -> Drain<A>:
  match mr:
    case None{}:
      DrDone{arr}
    case Some{root}:
      drain_last(~A, root, m, U32.is_eq(m, 0), Array.swap(Maybe<&2, A>, arr, m, None{}))

def drain_take(~A: Data, +m: U32, r: Array<Maybe<&2, A>> & Maybe<&2, A>) -> Drain<A>:
  (arr, mr) = r
  drain_root(~A, arr, m, mr)

# Take the root out of a copy holding `n` elements.
def drain_probe(~A: Data, +n: U32, arr: Array<Maybe<&2, A>>) -> Drain<A>:
  drain_take(~A, U32.sub(n, 1), Array.get(Maybe<&2, A>, arr, 0))

def drain_go(~A: Data, ~cmp: A -> A -> Cmp, fuel: Nat, +depth: Nat, st: Drain<A>) -> List<&2, A>:
  match fuel st:
    case _ DrDone{arr}:
      burn(~A, arr)
    case _ DrLast{arr, root}:
      burn_cons(~A, root, arr)
    case 0n DrMore{arr, root, m, last}:
      burn_cons(~A, root, arr)
    case 1n+f DrMore{arr, root, +m, last}:
      Con{root, drain_go(~A, ~cmp, f, depth, drain_probe(~A, m, sift_down(~A, ~cmp, depth, m, 0, last, arr)))}

def sorted_of(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +n: U32, +depth: Nat, cap: U32, c: Array<Maybe<&2, A>> & Array<Maybe<&2, A>>) -> Heap<A> & List<&2, A>:
  (arr, copy) = c
  (BH{size, n, depth, cap, arr}, drain_go(~A, ~cmp, size, depth, drain_probe(~A, n, copy)))

def to_sorted_list(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>) -> Heap<A> & List<&2, A>:
  BH{+size, +n, +depth, +cap, arr} = h
  sorted_of(~A, ~cmp, size, n, depth, cap, Array.clone(Maybe<&2, A>, arr))

# ---- operation traces ----

def obs_nat(~A: Data, r: Heap<A> & Nat) -> Heap<A> & E.Obs<A>:
  (h, n) = r
  (h, E.ONat{n})

def obs_item(~A: Data, r: Heap<A> & Result<&2, &2, E.Error, A>) -> Heap<A> & E.Obs<A>:
  (h, x) = r
  (h, E.OItem{x})

def obs_list(~A: Data, r: Heap<A> & List<&2, A>) -> Heap<A> & E.Obs<A>:
  (h, xs) = r
  (h, E.OList{xs})

def drop_heap(~A: Data, h: Heap<A>, v: Heap<A> & E.Obs<A>) -> Heap<A> & E.Obs<A>:
  v

# FromList replaces the heap: the old block is dropped (O(1) erasure).
def replace(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>, xs: List<&2, A>) -> Heap<A> & E.Obs<A>:
  BH{size, n, depth, cap, arr} = h
  (from_list(~A, ~cmp, xs), E.OUnit{})

def step(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>, op: E.Op<A>) -> Heap<A> & E.Obs<A>:
  match op:
    case E.Length{}:
      obs_nat(~A, length(~A, h))
    case E.Push{x}:
      (push(~A, ~cmp, h, x), E.OUnit{})
    case E.Peek{}:
      obs_item(~A, peek(~A, h))
    case E.Pop{}:
      obs_item(~A, pop(~A, ~cmp, h))
    case E.FromList{xs}:
      replace(~A, ~cmp, h, xs)
    case E.ToSortedList{}:
      obs_list(~A, to_sorted_list(~A, ~cmp, h))

def record(~A: Data, acc: List<&2, E.Obs<A>>, r: Heap<A> & E.Obs<A>) -> Heap<A> & List<&2, E.Obs<A>>:
  (h, o) = r
  (h, Con{o, acc})

def step_acc(~A: Data, ~cmp: A -> A -> Cmp, op: E.Op<A>, st: Heap<A> & List<&2, E.Obs<A>>) -> Heap<A> & List<&2, E.Obs<A>>:
  (h, acc) = st
  record(~A, acc, step(~A, ~cmp, h, op))

def run_acc(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, st: Heap<A> & List<&2, E.Obs<A>>) -> Heap<A> & List<&2, E.Obs<A>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~A, ~cmp, rest, step_acc(~A, ~cmp, op, st))

def finish(~A: Data, st: Heap<A> & List<&2, E.Obs<A>>) -> Heap<A> & List<&2, E.Obs<A>>:
  (h, acc) = st
  (h, List.reverse(&2, E.Obs<A>, acc))

def run(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, h: Heap<A>) -> Heap<A> & List<&2, E.Obs<A>>:
  finish(~A, run_acc(~A, ~cmp, ops, (h, Nil{})))

# ---- checked instances (proofs/binary_heap.bend) ----

def run_u32(ops: List<&2, E.Op<U32>>, h: Heap<U32>) -> Heap<U32> & List<&2, E.Obs<U32>>:
  run(~U32, ~U32.cmp, ops, h)

def run_string(ops: List<&2, E.Op<String>>, h: Heap<String>) -> Heap<String> & List<&2, E.Obs<String>>:
  run(~String, ~String.order, ops, h)
