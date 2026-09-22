import Base
import ../../types/internal_dlist.bend as E

# Doubly linked list with stable opaque handles, values of an erased type T.
#
# Representation: PARALLEL INDEXED ARENAS. Three `Base.Array` blocks of
# 2^depth slots share one index space:
#   vals   Maybe<T>  the element stored at an id (None: never used or removed)
#   prevs  U32       the LINK to the preceding element
#   nexts  U32       the LINK to the following element
# A link is id + 1, and `nil()` = 0 is the "no neighbour" link (as are the
# head and tail fields), so testing for a neighbour is a comparison with 0
# and following a link is one subtraction. Ids are slot indices below 2^31,
# so id + 1 never wraps. The element id IS its slot index;
# ids come from a monotone counter and are never reused, so a handle to a
# removed element is stale (its `vals` slot is None) and a handle whose tag
# differs from the list's is foreign. The blocks double when the counter
# reaches the capacity (the old block becomes the lower half, so every id
# keeps its slot), exactly as the dynamic array grows.
#
# The prev/next links are the doubly linked list's own links - what the
# structure is for - stored as arena indices. Keeping them in their own
# blocks makes relinking a neighbour ONE indexed write (no read-modify-write
# of a node record). Nothing is stored in a search tree or a cons list.
#
# Cost (n = number of elements ever inserted): every handle operation and
# push is O(1) indexed reads and writes; `length` is the cached count;
# `to_list` reads O(count) slots. A push that finds the blocks full doubles
# them (one `Base.Array` node and one fresh half per block), amortised O(1).
# Because ids are never reused the blocks grow with n, not with the live
# count - the same trade the reference C implementation makes.
#
# Errors: a foreign handle gives Fail{ForeignHandle}, a stale one
# Fail{StaleHandle}; every failure returns the list unchanged.

type DList<-T: Data> is Type:
  DL{tag: U32, fresh: U32, free: U32, count: Nat, head: U32, tail: U32, depth: Nat, cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>}

def nil() -> U32:
  0

# The link to an element, and the element a (non-nil) link points to.
def link(+i: U32) -> U32:
  U32.inc(i)

def slot(+l: U32) -> U32:
  U32.sub(l, 1)

def new_vals(~T: Data, +depth: Nat) -> Array<Maybe<&2, T>>:
  Array.new(Maybe<&2, T>, depth, None{})

def new_links(+depth: Nat) -> Array<U32>:
  Array.new(U32, depth, nil())

def new(~T: Data, tag: U32) -> DList<T>:
  DL{tag, 0, 0, 0n, nil(), nil(), 0n, 1, new_vals(~T, 0n), new_links(0n), new_links(0n)}

# A link as the Maybe the public API reports.
def pick_link(none: Bool, +l: U32) -> Maybe<&2, U32>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{l}

# ---- relinking ----

# Point the link stored at element a (if a is a link, not nil) at q.
def link_of(+l: U32) -> Maybe<&2, U32>:
  pick_link(U32.is_eq(l, nil()), l)

def set_next_go(nexts: Array<U32>, +a: U32, +q: U32, none: Bool) -> Array<U32>:
  match none:
    case True{}:
      nexts
    case False{}:
      Array.set(U32, nexts, slot(a), q)

# ---- insertion ----

def set_next(nexts: Array<U32>, +a: U32, +q: U32) -> Array<U32>:
  set_next_go(nexts, a, q, U32.is_eq(a, nil()))

def grown_vals(~T: Data, +depth: Nat, a: Array<Maybe<&2, T>>) -> Array<Maybe<&2, T>>:
  ANode{a, new_vals(~T, depth)}

def grown_links(+depth: Nat, a: Array<U32>) -> Array<U32>:
  ANode{a, new_links(depth)}

# Store x at slot n between the links a and b (either may be nil) and relink them.
def link_in(~T: Data, +tag: U32, +n: U32, +nfresh: U32, +nfree: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +a: U32, +b: U32, x: T) -> DList<T> & E.Handle:
  (DL{tag, nfresh, nfree, 1n+count, pick_end(U32.is_eq(a, nil()), link(n), head), pick_end(U32.is_eq(b, nil()), link(n), tail), depth, cap,
      Array.set(Maybe<&2, T>, vals, n, Some{x}),
      set_next(Array.set(U32, prevs, n, a), b, link(n)),
      set_next(Array.set(U32, nexts, n, b), a, link(n))}, E.H{tag, n})

# The end pointer after linking n next to a (nil: n becomes that end).
def pick_end(none: Bool, +n: U32, +e: U32) -> U32:
  match none:
    case True{}:
      n
    case False{}:
      e

def insert_room(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +a: U32, +b: U32, x: T, room: Bool) -> DList<T> & E.Handle:
  match room:
    case True{}:
      link_in(~T, tag, fresh, U32.inc(fresh), free, count, head, tail, depth, cap, vals, prevs, nexts, a, b, x)
    case False{}:
      link_in(~T, tag, fresh, U32.inc(fresh), free, count, head, tail, 1n+depth, U32.shl(cap), grown_vals(~T, depth, vals), grown_links(depth, prevs), grown_links(depth, nexts), a, b, x)

def insert_between(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +a: U32, +b: U32, x: T) -> DList<T> & E.Handle:
  insert_room(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, a, b, x, U32.is_lt(fresh, cap))

def length(~T: Data, s: DList<T>) -> DList<T> & Nat:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, count)

def push_front(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  insert_between(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, nil(), head, x)

def push_back(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  insert_between(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, tail, nil(), x)

def done_handle(~T: Data, r: DList<T> & E.Handle) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (s, h) = r
  (s, Done{h})

# ---- validating a handle ----
#
# `live(i)` reads the value slot; every handle operation branches on it.

def fail_same(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, e: E.Error) -> DList<T> & E.Error:
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, e)

# The neighbour link on one side of a live element.
def link_at(links: Array<U32>, +i: U32) -> Array<U32> & U32:
  Array.get(U32, links, i)

def ins_side(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, +p: U32, +n: U32, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match after:
    case False{}:
      done_handle(~T, insert_between(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, p, link(i), x))
    case True{}:
      done_handle(~T, insert_between(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, link(i), n, x))

def ins_live2(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, +i: U32, x: T, pr: Array<U32> & U32, nx: Array<U32> & U32) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (prevs, p) = pr
  (nexts, n) = nx
  ins_side(~T, after, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, p, n, x)

def ins_found(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, x: T, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (vals, m) = r
  match m:
    case None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case Some{v}:
      ins_live2(~T, after, tag, fresh, free, count, head, tail, depth, cap, vals, i, x, link_at(prevs, i), link_at(nexts, i))

def insert_checked(~T: Data, after: Bool, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, x: T, same: Bool) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      ins_found(~T, after, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, i, x, Array.get(Maybe<&2, T>, vals, i))

def insert_before(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  insert_checked(~T, False{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, x, U32.is_eq(l, tag))

def insert_after(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  insert_checked(~T, True{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, x, U32.is_eq(l, tag))

# ---- removal ----

def rm_links(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, +v: T, pr: Array<U32> & U32, nx: Array<U32> & U32) -> DList<T> & Result<&2, &2, E.Error, T>:
  (prevs, +p) = pr
  (nexts, +n) = nx
  (DL{tag, fresh, free, Nat.sub(count, 1n), pick_end(U32.is_eq(p, nil()), n, head), pick_end(U32.is_eq(n, nil()), p, tail), depth, cap,
      vals, set_next(prevs, n, p), set_next(nexts, p, n)}, Done{v})

def rm_found(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, T>:
  (vals, m) = r
  match m:
    case None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case Some{+v}:
      rm_links(~T, tag, fresh, free, count, head, tail, depth, cap, Array.set(Maybe<&2, T>, vals, i, None{}), v, link_at(prevs, i), link_at(nexts, i))

def remove_checked(~T: Data, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, same: Bool) -> DList<T> & Result<&2, &2, E.Error, T>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      rm_found(~T, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, i, Array.get(Maybe<&2, T>, vals, i))

def remove(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  remove_checked(~T, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, U32.is_eq(l, tag))

# ---- reading and writing one element ----

def value_of(~T: Data, m: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match m:
    case None{}:
      Fail{E.StaleHandle{}}
    case Some{v}:
      Done{v}

def get_fin(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, T>:
  (vals, m) = r
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, value_of(~T, m))

def get_checked(~T: Data, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, same: Bool) -> DList<T> & Result<&2, &2, E.Error, T>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      get_fin(~T, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, Array.get(Maybe<&2, T>, vals, i))

def get(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  get_checked(~T, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, U32.is_eq(l, tag))

def set_fin(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, x: T, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  (vals, m) = r
  match m:
    case None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, Array.set(Maybe<&2, T>, vals, i, None{}), prevs, nexts}, Fail{E.StaleHandle{}})
    case Some{v}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Done{Unit{}})

# set swaps the new value in: one indexed access when the element is live;
# a stale slot is None and is written back as None.
def set_checked(~T: Data, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, +x: T, same: Bool) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      set_fin(~T, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, i, x, Array.swap(Maybe<&2, T>, vals, i, Some{x}))

def set(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  set_checked(~T, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, x, U32.is_eq(l, tag))

# ---- neighbours ----

def handle_go(+tag: U32, +l: U32, none: Bool) -> Maybe<&2, E.Handle>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{E.H{tag, slot(l)}}

def handle(+tag: U32, +l: U32) -> Maybe<&2, E.Handle>:
  handle_go(tag, l, U32.is_eq(l, nil()))

def nbr_n(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, r: Array<U32> & U32) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  (nexts, +n) = r
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Done{handle(tag, n)})

def nbr_p(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, nexts: Array<U32>, r: Array<U32> & U32) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  (prevs, +p) = r
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Done{handle(tag, p)})

def nbr_fin(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, m: Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match after m:
    case _ None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} Some{v}:
      nbr_n(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, link_at(nexts, i))
    case False{} Some{v}:
      nbr_p(~T, tag, fresh, free, count, head, tail, depth, cap, vals, nexts, link_at(prevs, i))

def nbr_read(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  (vals, m) = r
  nbr_fin(~T, after, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, m)

def nbr_checked(~T: Data, after: Bool, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, same: Bool) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      nbr_read(~T, after, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, i, Array.get(Maybe<&2, T>, vals, i))

def next(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  nbr_checked(~T, True{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, U32.is_eq(l, tag))

def prev(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  nbr_checked(~T, False{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, U32.is_eq(l, tag))

# ---- to_list ----
#
# Walk BACKWARDS from the tail, consing onto an accumulator, so the list
# comes out in order and the walk is a tail call; the count bounds it.

# One loop, no mutual recursion: the state carries the next id to read.
type Cur<-T: Data> is Type:
  C{vals: Array<Maybe<&2, T>>, prevs: Array<U32>, acc: List<&2, T>, at: U32}

def step_p(~T: Data, vals: Array<Maybe<&2, T>>, acc: List<&2, T>, r: Array<U32> & U32) -> Cur<T>:
  (prevs, p) = r
  C{vals, prevs, acc, p}

def step_m(~T: Data, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, acc: List<&2, T>, +at: U32, m: Maybe<&2, T>) -> Cur<T>:
  match m:
    case None{}:
      C{vals, prevs, acc, nil()}
    case Some{v}:
      step_p(~T, vals, Con{v, acc}, Array.get(U32, prevs, slot(at)))

def step_v(~T: Data, prevs: Array<U32>, acc: List<&2, T>, +at: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> Cur<T>:
  (vals, m) = r
  step_m(~T, vals, prevs, acc, at, m)

def step_back(~T: Data, c: Cur<T>) -> Cur<T>:
  C{vals, prevs, acc, +at} = c
  step_v(~T, prevs, acc, at, Array.get(Maybe<&2, T>, vals, slot(at)))

def walk(~T: Data, fuel: Nat, c: Cur<T>) -> Cur<T>:
  match fuel:
    case 0n:
      c
    case 1n+f:
      walk(~T, f, step_back(~T, c))

def tl_fin(~T: Data, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, nexts: Array<U32>, c: Cur<T>) -> DList<T> & List<&2, T>:
  C{vals, prevs, acc, at} = c
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, acc)

def to_list(~T: Data, s: DList<T>) -> DList<T> & List<&2, T>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  tl_fin(~T, tag, fresh, free, count, head, tail, depth, cap, nexts, walk(~T, count, C{vals, prevs, Nil{}, tail}))

# ---- recycling end operations: the deque's storage API ----
#
# `free` is a STACK of retired slots chained through `nexts`: the record's
# field is the link to the top (nil() = empty) and `nexts[s]` of a retired
# slot s is the link to the next retired one. A retired slot holds None in
# `vals` and is not in the list.
#
# The handle-stable API above NEVER touches this stack: its ids come from the
# monotone `fresh` counter and are never reused, so a handle to a removed
# element stays unambiguously stale (the objective's handle contract). The
# operations below DO recycle, and they are the storage operations
# src/deque.bend runs on: a deque exposes no handles at all, so reissuing an
# id is unobservable through it, and the arenas then grow with the PEAK
# number of live elements instead of with the number of pushes. They are not
# members of `Op`, so the list's trace laws are unaffected by them; they have
# component laws under proofs/dlist/reuse_*.bend and free_chain.bend.
# The general deque refinement is still being composed.
#
# Every one of them is O(1) indexed reads and writes.

# Allocate the top of the free stack: `nx` is the link it stored, which
# becomes the new top. `nexts[i]` is overwritten by `link_in`, after the read.
def ins_free_pop(~T: Data, +tag: U32, +fresh: U32, +f: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, +a: U32, +b: U32, x: T, r: Array<U32> & U32) -> DList<T> & E.Handle:
  (nexts, +nx) = r
  link_in(~T, tag, slot(f), fresh, nx, count, head, tail, depth, cap, vals, prevs, nexts, a, b, x)

def ins_free_pick(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +a: U32, +b: U32, x: T, empty: Bool) -> DList<T> & E.Handle:
  match empty:
    case True{}:
      insert_between(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, a, b, x)
    case False{}:
      ins_free_pop(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, a, b, x, link_at(nexts, slot(free)))

def insert_between_free(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +a: U32, +b: U32, x: T) -> DList<T> & E.Handle:
  ins_free_pick(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, a, b, x, U32.is_eq(free, nil()))

def push_front_free(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  insert_between_free(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, nil(), head, x)

def push_back_free(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  insert_between_free(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, tail, nil(), x)

# Unlink the element at slot i and push i on the free stack. `set_next` writes
# at the NEIGHBOUR slots (both different from i), so the last write, which
# stores the old top in nexts[i], cannot be overwritten.
def rmf_links(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, +i: U32, v: T, pr: Array<U32> & U32, nx: Array<U32> & U32) -> DList<T> & Maybe<&2, T>:
  (prevs, +p) = pr
  (nexts, +n) = nx
  (DL{tag, fresh, link(i), Nat.sub(count, 1n), pick_end(U32.is_eq(p, nil()), n, head), pick_end(U32.is_eq(n, nil()), p, tail), depth, cap,
      vals, set_next(prevs, n, p), Array.set(U32, set_next(nexts, p, n), i, free)}, Some{v})

def rmf_found(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Maybe<&2, T>:
  (vals, m) = r
  match m:
    case None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, None{})
    case Some{v}:
      rmf_links(~T, tag, fresh, free, count, head, tail, depth, cap, Array.set(Maybe<&2, T>, vals, i, None{}), i, v, link_at(prevs, i), link_at(nexts, i))

def pop_end(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +l: U32, empty: Bool) -> DList<T> & Maybe<&2, T>:
  match empty:
    case True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, None{})
    case False{}:
      rmf_found(~T, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, slot(l), Array.get(Maybe<&2, T>, vals, slot(l)))

def pop_front_free(~T: Data, s: DList<T>) -> DList<T> & Maybe<&2, T>:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  pop_end(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, head, U32.is_eq(head, nil()))

def pop_back_free(~T: Data, s: DList<T>) -> DList<T> & Maybe<&2, T>:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  pop_end(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, tail, U32.is_eq(tail, nil()))

def peek_fin(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Maybe<&2, T>:
  (vals, m) = r
  (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, m)

def peek_end(~T: Data, +tag: U32, +fresh: U32, +free: U32, count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +l: U32, empty: Bool) -> DList<T> & Maybe<&2, T>:
  match empty:
    case True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, None{})
    case False{}:
      peek_fin(~T, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, Array.get(Maybe<&2, T>, vals, slot(l)))

def peek_front(~T: Data, s: DList<T>) -> DList<T> & Maybe<&2, T>:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  peek_end(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, head, U32.is_eq(head, nil()))

def peek_back(~T: Data, s: DList<T>) -> DList<T> & Maybe<&2, T>:
  DL{+tag, +fresh, +free, count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  peek_end(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, tail, U32.is_eq(tail, nil()))

# ---- trace runner ----

def obs_nat(~T: Data, r: DList<T> & Nat) -> DList<T> & E.Obs<T>:
  (s, n) = r
  (s, E.ONat{n})

def obs_handle(~T: Data, r: DList<T> & E.Handle) -> DList<T> & E.Obs<T>:
  (s, h) = r
  (s, E.OHandle{h})

def obs_insert(~T: Data, r: DList<T> & Result<&2, &2, E.Error, E.Handle>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OInsert{x})

def obs_val(~T: Data, r: DList<T> & Result<&2, &2, E.Error, T>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OVal{x})

def obs_unit(~T: Data, r: DList<T> & Result<&2, &2, E.Error, Unit>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OUnit{x})

def obs_nbr(~T: Data, r: DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.ONbr{x})

def obs_list(~T: Data, r: DList<T> & List<&2, T>) -> DList<T> & E.Obs<T>:
  (s, xs) = r
  (s, E.OList{xs})

def step(~T: Data, s: DList<T>, op: E.Op<T>) -> DList<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(~T, length(~T, s))
    case E.PushFront{x}:
      obs_handle(~T, push_front(~T, s, x))
    case E.PushBack{x}:
      obs_handle(~T, push_back(~T, s, x))
    case E.InsertBefore{h, x}:
      obs_insert(~T, insert_before(~T, s, h, x))
    case E.InsertAfter{h, x}:
      obs_insert(~T, insert_after(~T, s, h, x))
    case E.Remove{h}:
      obs_val(~T, remove(~T, s, h))
    case E.Get{h}:
      obs_val(~T, get(~T, s, h))
    case E.Set{h, x}:
      obs_unit(~T, set(~T, s, h, x))
    case E.Next{h}:
      obs_nbr(~T, next(~T, s, h))
    case E.Prev{h}:
      obs_nbr(~T, prev(~T, s, h))
    case E.ToList{}:
      obs_list(~T, to_list(~T, s))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: DList<T> & E.Obs<T>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  record(~T, acc, step(~T, s, op))

def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs<T>, acc))

def run(~T: Data, ops: List<&2, E.Op<T>>, s: DList<T>) -> DList<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (s, Nil{})))

# Internal insertion variants for a generational public handle owner.
def ins_side_reuse(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, +p: U32, +n: U32, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match after:
    case False{}:
      done_handle(~T, insert_between_free(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, p, link(i), x))
    case True{}:
      done_handle(~T, insert_between_free(~T, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, link(i), n, x))

def ins_live2_reuse(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, +i: U32, x: T, pr: Array<U32> & U32, nx: Array<U32> & U32) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (prevs, p) = pr
  (nexts, n) = nx
  ins_side_reuse(~T, after, tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, p, n, x)

def ins_found_reuse(~T: Data, after: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, prevs: Array<U32>, nexts: Array<U32>, +i: U32, x: T, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (vals, m) = r
  match m:
    case None{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case Some{v}:
      ins_live2_reuse(~T, after, tag, fresh, free, count, head, tail, depth, cap, vals, i, x, link_at(prevs, i), link_at(nexts, i))

def insert_checked_reuse(~T: Data, after: Bool, ok: Bool, +tag: U32, +fresh: U32, +free: U32, +count: Nat, +head: U32, +tail: U32, +depth: Nat, +cap: U32, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +i: U32, x: T, same: Bool) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match ok same:
    case _ False{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.ForeignHandle{}})
    case False{} True{}:
      (DL{tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts}, Fail{E.StaleHandle{}})
    case True{} True{}:
      ins_found_reuse(~T, after, tag, fresh, free, count, head, tail, depth, cap, prevs, nexts, i, x, Array.get(Maybe<&2, T>, vals, i))

def insert_before_reuse(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  insert_checked_reuse(~T, False{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, x, U32.is_eq(l, tag))

def insert_after_reuse(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  DL{+tag, +fresh, +free, +count, +head, +tail, +depth, +cap, vals, prevs, nexts} = s
  E.H{+l, +i} = h
  insert_checked_reuse(~T, True{}, U32.is_lt(i, fresh), tag, fresh, free, count, head, tail, depth, cap, vals, prevs, nexts, i, x, U32.is_eq(l, tag))


# Called only after a successful remove, by an owner that invalidated the
# removed handle's generation. The slot is already absent from the live list.
def recycle_slot(~T: Data, s: DList<T>, +i: U32) -> DList<T>:
  DL{tag, fresh, +free, count, head, tail, depth, cap, vals, prevs, nexts} = s
  DL{tag, fresh, link(i), count, head, tail, depth, cap, vals, prevs, Array.set(U32, nexts, i, free)}
