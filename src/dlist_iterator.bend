import Base
import ./doubly_linked_list.bend as D
import ./internal/dlist_storage.bend as R
import ../types/doubly_linked_list.bend as E
import ../types/internal_dlist.bend as H

def choose(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# Owning, bidirectional gap cursor. The list cannot be used independently until
# finish() returns it. last is cleared by add/remove, retained by set and seeks.
type Error is Data:
  Exhausted{}
  NoCurrent{}
  Storage{error: E.Error}

type Iterator<-T: Data> is Type:
  IT{list: D.DList<T>, next: U32, last: U32, forward: Bool, index: Nat}

# Cursor links are arena indices plus one; zero is the gap past the end.
# Only this owning iterator can mutate the list until finish. Public handles
# retain their owner and generation; a cursor is never exposed as a handle.
def endpoint(~T: Data, s: D.DList<T>, +front: Bool) -> D.DList<T> & U32:
  D.DL{tag, depth, cap, raw, gens} = s
  R.DL{owner, fresh, free, count, +head, +tail, rd, rc, vals, prevs, nexts} = raw
  (D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, choose(U32, front, head, tail))

def first_result(~T: Data, r: D.DList<T> & U32) -> Iterator<T>:
  (s, h) = r
  IT{s, h, 0, True{}, 0n}

def iter_first(~T: Data, s: D.DList<T>) -> Iterator<T>:
  first_result(~T, endpoint(~T, s, True{}))

def last_result(~T: Data, r: D.DList<T> & Nat) -> Iterator<T>:
  (s, n) = r
  IT{s, 0, 0, True{}, n}

def iter_last(~T: Data, s: D.DList<T>) -> Iterator<T>:
  last_result(~T, D.length(~T, s))

def finish(~T: Data, it: Iterator<T>) -> D.DList<T>:
  IT{s, n, last, f, i} = it
  s

def present(h: U32) -> Bool:
  U32.is_lt(0, h)

def has_next(~T: Data, it: Iterator<T>) -> Iterator<T> & Bool:
  IT{s, +n, last, f, i} = it
  (IT{s, n, last, f, i}, present(n))

def has_previous(~T: Data, it: Iterator<T>) -> Iterator<T> & Bool:
  IT{s, n, last, f, +i} = it
  (IT{s, n, last, f, i}, Nat.is_lt(0n, i))

def position(~T: Data, it: Iterator<T>) -> Iterator<T> & Nat:
  IT{s, n, last, f, +i} = it
  (IT{s, n, last, f, i}, i)

def cursor_set(~T: Data, s: D.DList<T>, link: U32, x: T) -> D.DList<T> & Result<&2, &2, E.Error, Unit>:
  D.DL{+tag, depth, cap, raw, gens} = s
  D.set_result(~T, tag, depth, cap, gens, R.set(~T, raw, H.H{tag, U32.sub(link, 1)}, x))

def cursor_remove_gen(~T: Data, +tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, +id: U32, r: Array<U32> & U32) -> D.DList<T> & Result<&2, &2, E.Error, T>:
  (gens, generation) = r
  D.project_value(~T, D.removed(~T, tag, depth, cap, gens, id, generation, R.remove(~T, raw, H.H{tag, id})))

def cursor_remove(~T: Data, s: D.DList<T>, +link: U32) -> D.DList<T> & Result<&2, &2, E.Error, T>:
  D.DL{tag, depth, cap, raw, gens} = s
  cursor_remove_gen(~T, tag, depth, cap, raw, U32.sub(link, 1), Array.get(U32, gens, U32.sub(link, 1)))

def gap_left(prevs: Array<U32>, tail: U32, n: U32, empty: Bool) -> Array<U32> & U32:
  match empty:
    case True{}:
      (prevs, tail)
    case False{}:
      Array.get(U32, prevs, U32.sub(n, 1))

def insert_gap_result(~T: Data, r: D.DList<T> & E.Handle) -> D.DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (s, h) = r
  (s, Done{h})

def insert_gap(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, owner: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, rd: Nat, rc: U32, vals: Array<Maybe<&2, T>>, nexts: Array<U32>, n: U32, x: T, r: Array<U32> & U32) -> D.DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (prevs, before) = r
  insert_gap_result(~T, D.inserted(~T, tag, depth, cap, gens, R.insert_between_free(~T, owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts, before, n, x)))

# n is a live cursor link, or zero for the gap following the tail.
def cursor_insert_gap(~T: Data, s: D.DList<T>, +n: U32, x: T) -> D.DList<T> & Result<&2, &2, E.Error, E.Handle>:
  D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, +tail, rd, rc, vals, prevs, nexts}, gens} = s
  insert_gap(~T, tag, depth, cap, gens, owner, fresh, free, count, head, tail, rd, rc, vals, nexts, n, x, gap_left(prevs, tail, n, U32.is_eq(n, 0)))

type Move<-T: Data> is Data:
  M{next: U32, last: U32, forward: Bool, index: Nat, result: Result<&2, &2, Error, T>}

def move_meta(~T: Data, n: U32, last: U32, f: Bool, +i: Nat, h: U32, next: U32, +forward: Bool, r: Result<&2, &2, Error, T>) -> Move<T>:
  match r:
    case Fail{e}:
      M{n, last, f, i, Fail{e}}
    case Done{x}:
      M{next, h, forward, choose(Nat, forward, 1n+i, Nat.sub(i, 1n)), Done{x}}

def attach_move(~T: Data, s: D.DList<T>, m: Move<T>) -> Iterator<T> & Result<&2, &2, Error, T>:
  M{n, last, f, i, out} = m
  (IT{s, n, last, f, i}, out)

def storage_result(~T: Data, r: Result<&2, &2, E.Error, T>) -> Result<&2, &2, Error, T>:
  match r:
    case Fail{e}:
      Fail{Storage{e}}
    case Done{x}:
      Done{x}

type Forward<-T: Data> is Type:
  F{vals: Array<Maybe<&2, T>>, nexts: Array<U32>, after: U32, value: Result<&2, &2, Error, T>}

def forward_link(~T: Data, vals: Array<Maybe<&2, T>>, value: Maybe<&2, T>, r: Array<U32> & U32) -> Forward<T>:
  (nexts, after) = r
  F{vals, nexts, after, storage_result(~T, D.item_result(~T, R.value_of(~T, value)))}

def forward_value(~T: Data, nexts: Array<U32>, n: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Forward<T>:
  (vals, value) = r
  forward_link(~T, vals, value, Array.get(U32, nexts, U32.sub(n, 1)))

def forward_arrays(~T: Data, vals: Array<Maybe<&2, T>>, nexts: Array<U32>, +n: U32, empty: Bool) -> Forward<T>:
  match empty:
    case True{}:
      F{vals, nexts, 0, Fail{Exhausted{}}}
    case False{}:
      forward_value(~T, nexts, n, Array.get(Maybe<&2, T>, vals, U32.sub(n, 1)))

def forward_finish(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, owner: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, rd: Nat, rc: U32, prevs: Array<U32>, +n: U32, last: U32, f: Bool, i: Nat, r: Forward<T>) -> Iterator<T> & Result<&2, &2, Error, T>:
  F{vals, nexts, after, value} = r
  attach_move(~T, D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, move_meta(~T, n, last, f, i, n, after, True{}, value))

def next_checked(~T: Data, it: Iterator<T>, empty: Bool) -> Iterator<T> & Result<&2, &2, Error, T>:
  IT{D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, +n, last, f, i} = it
  forward_finish(~T, tag, depth, cap, gens, owner, fresh, free, count, head, tail, rd, rc, prevs, n, last, f, i, forward_arrays(~T, vals, nexts, n, empty))

def next(~T: Data, it: Iterator<T>) -> Iterator<T> & Result<&2, &2, Error, T>:
  IT{s, +n, last, f, i} = it
  next_checked(~T, IT{s, n, last, f, i}, U32.is_eq(n, 0))

def backward_value_result(~T: Data, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Array<Maybe<&2, T>> & Result<&2, &2, Error, T>:
  (vals, value) = r
  (vals, storage_result(~T, D.item_result(~T, R.value_of(~T, value))))

def backward_value(~T: Data, vals: Array<Maybe<&2, T>>, h: U32, empty: Bool) -> Array<Maybe<&2, T>> & Result<&2, &2, Error, T>:
  match empty:
    case True{}:
      (vals, Fail{Exhausted{}})
    case False{}:
      backward_value_result(~T, Array.get(Maybe<&2, T>, vals, U32.sub(h, 1)))

def backward_finish(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, owner: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, rd: Nat, rc: U32, prevs: Array<U32>, nexts: Array<U32>, n: U32, last: U32, f: Bool, i: Nat, +h: U32, r: Array<Maybe<&2, T>> & Result<&2, &2, Error, T>) -> Iterator<T> & Result<&2, &2, Error, T>:
  (vals, value) = r
  attach_move(~T, D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, move_meta(~T, n, last, f, i, h, h, False{}, value))

def previous_found(~T: Data, n: U32, last: U32, f: Bool, i: Nat, r: D.DList<T> & U32) -> Iterator<T> & Result<&2, &2, Error, T>:
  (D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, +h) = r
  backward_finish(~T, tag, depth, cap, gens, owner, fresh, free, count, head, tail, rd, rc, prevs, nexts, n, last, f, i, h, backward_value(~T, vals, h, U32.is_eq(h, 0)))

def previous_target(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, owner: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, rd: Nat, rc: U32, vals: Array<Maybe<&2, T>>, nexts: Array<U32>, n: U32, last: U32, f: Bool, i: Nat, r: Array<U32> & U32) -> Iterator<T> & Result<&2, &2, Error, T>:
  (prevs, target) = r
  previous_found(~T, n, last, f, i, (D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, target))

def previous_checked(~T: Data, it: Iterator<T>, empty: Bool) -> Iterator<T> & Result<&2, &2, Error, T>:
  IT{D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, +tail, rd, rc, vals, prevs, nexts}, gens}, +n, last, f, i} = it
  previous_target(~T, tag, depth, cap, gens, owner, fresh, free, count, head, tail, rd, rc, vals, nexts, n, last, f, i, gap_left(prevs, tail, n, empty))

def previous(~T: Data, it: Iterator<T>) -> Iterator<T> & Result<&2, &2, Error, T>:
  IT{s, +n, last, f, i} = it
  previous_checked(~T, IT{s, n, last, f, i}, U32.is_eq(n, 0))

def set_result(~T: Data, n: U32, last: U32, f: Bool, i: Nat, r: D.DList<T> & Result<&2, &2, E.Error, Unit>) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  match r:
    case Tuple{s, Fail{e}}:
      (IT{s, n, last, f, i}, Fail{Storage{e}})
    case Tuple{s, Done{x}}:
      (IT{s, n, last, f, i}, Done{Unit{}})

def set_checked(~T: Data, it: Iterator<T>, x: T, empty: Bool) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  match it empty:
    case IT{s, n, last, f, i} True{}:
      (IT{s, n, 0, f, i}, Fail{NoCurrent{}})
    case IT{s, n, +h, f, i} False{}:
      set_result(~T, n, h, f, i, cursor_set(~T, s, h, x))

def add_meta(n: U32, last: U32, f: Bool, i: Nat, r: Result<&2, &2, E.Error, E.Handle>) -> Move<Unit>:
  match r:
    case Fail{e}:
      M{n, last, f, i, Fail{Storage{e}}}
    case Done{h}:
      M{n, 0, f, 1n+i, Done{Unit{}}}

def attach_unit(~T: Data, s: D.DList<T>, m: Move<Unit>) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  M{n, last, f, i, out} = m
  (IT{s, n, last, f, i}, out)

def added(~T: Data, n: U32, last: U32, f: Bool, i: Nat, r: D.DList<T> & Result<&2, &2, E.Error, E.Handle>) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  (s, out) = r
  attach_unit(~T, s, add_meta(n, last, f, i, out))

def add(~T: Data, it: Iterator<T>, x: T) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  IT{s, +n, last, f, i} = it
  added(~T, n, last, f, i, cursor_insert_gap(~T, s, n, x))

def remove_meta(~T: Data, n: U32, last: U32, +f: Bool, +i: Nat, after: U32, r: Result<&2, &2, E.Error, T>) -> Move<Unit>:
  match r:
    case Fail{e}:
      M{n, last, f, i, Fail{Storage{e}}}
    case Done{x}:
      M{after, 0, f, choose(Nat, f, Nat.sub(i, 1n), i), Done{Unit{}}}

def removed(~T: Data, n: U32, last: U32, f: Bool, i: Nat, after: U32, r: D.DList<T> & Result<&2, &2, E.Error, T>) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  (s, out) = r
  attach_unit(~T, s, remove_meta(~T, n, last, f, i, after, out))

def remove_target(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, owner: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, rd: Nat, rc: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, n: U32, +h: U32, f: Bool, i: Nat, r: Array<U32> & U32) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  (nexts, after) = r
  removed(~T, n, h, f, i, after, cursor_remove(~T, D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, h))

def remove_checked(~T: Data, it: Iterator<T>, empty: Bool) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  match it empty:
    case IT{s, n, last, f, i} True{}:
      (IT{s, n, 0, f, i}, Fail{NoCurrent{}})
    case IT{D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}, +n, +h, +f, i} False{}:
      remove_target(~T, tag, depth, cap, gens, owner, fresh, free, count, head, tail, rd, rc, vals, prevs, n, h, f, i, gap_left(nexts, n, h, f))

def set(~T: Data, it: Iterator<T>, x: T) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  IT{s, n, +last, f, i} = it
  set_checked(~T, IT{s, n, last, f, i}, x, U32.is_eq(last, 0))

def remove(~T: Data, it: Iterator<T>) -> Iterator<T> & Result<&2, &2, Error, Unit>:
  IT{s, n, +last, f, i} = it
  remove_checked(~T, IT{s, n, last, f, i}, U32.is_eq(last, 0))

