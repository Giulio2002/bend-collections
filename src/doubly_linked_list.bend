import Base
import ../types/doubly_linked_list.bend as E
import ../types/balanced_search_tree.bend as BE
import ./balanced_search_tree.bend as B

# Doubly linked list with stable opaque handles, values of an erased type T.
# Representation: nodes {value, prev id, next id} in an ordered map keyed by
# element id (the Nat instance of src/balanced_search_tree.bend), plus head,
# tail, element count, the next fresh id and the list's tag. Ids are never
# reused, so a handle to a removed element is detected as stale; a handle
# whose tag differs from the list's is rejected as foreign. (Tags are chosen
# by the caller of new; lists that must reject each other's handles need
# distinct tags.) Every failure returns the state unchanged.
#
# Cost (n elements ever inserted): every handle operation, push and length
# O(log n) (map lookups/updates, a constant number per operation);
# to_list O(n log n).

type Node<-T: Data> is Data:
  N{val: T, prev: Maybe<&2, Nat>, next: Maybe<&2, Nat>}

type DList<-T: Data> is Data:
  DL{tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, Node<T>>}

def new(-T: Data, tag: Nat) -> DList<T>:
  DL{tag, 0n, 0n, None{}, None{}, B.new(Nat, Node<T>)}

def node(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, +i: Nat) -> Maybe<&2, Node<T>>:
  B.get(~Nat, ~Nat.cmp, Node<T>, nodes, i)

def nodeM(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, c: Maybe<&2, Nat>) -> Maybe<&2, Node<T>>:
  match c:
    case None{}:
      None{}
    case Some{+i}:
      node(T, nodes, i)

def put(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, +i: Nat, nd: Node<T>) -> B.OrdMap<Nat, Node<T>>:
  B.insert(~Nat, ~Nat.cmp, Node<T>, nodes, i, nd)

def drop(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, +i: Nat) -> B.OrdMap<Nat, Node<T>>:
  Pair.fst(B.OrdMap<Nat, Node<T>>, Result<&2, &2, BE.Error, Node<T>>, B.remove(~Nat, ~Nat.cmp, Node<T>, nodes, i))

def with_next(-T: Data, m: Maybe<&2, Node<T>>, +nodes: B.OrdMap<Nat, Node<T>>, +j: Nat, q: Maybe<&2, Nat>) -> B.OrdMap<Nat, Node<T>>:
  match m:
    case None{}:
      nodes
    case Some{N{v, p, n}}:
      put(T, nodes, j, N{v, p, q})

def set_next(-T: Data, +nodes: B.OrdMap<Nat, Node<T>>, a: Maybe<&2, Nat>, q: Maybe<&2, Nat>) -> B.OrdMap<Nat, Node<T>>:
  match a:
    case None{}:
      nodes
    case Some{+j}:
      with_next(T, node(T, nodes, j), nodes, j, q)

def with_prev(-T: Data, m: Maybe<&2, Node<T>>, +nodes: B.OrdMap<Nat, Node<T>>, +j: Nat, p: Maybe<&2, Nat>) -> B.OrdMap<Nat, Node<T>>:
  match m:
    case None{}:
      nodes
    case Some{N{v, p0, n}}:
      put(T, nodes, j, N{v, p, n})

def set_prev(-T: Data, +nodes: B.OrdMap<Nat, Node<T>>, b: Maybe<&2, Nat>, p: Maybe<&2, Nat>) -> B.OrdMap<Nat, Node<T>>:
  match b:
    case None{}:
      nodes
    case Some{+j}:
      with_prev(T, node(T, nodes, j), nodes, j, p)

# Store node n (value x) between a and b, relinking both neighbours.
def link(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +n: Nat, x: T) -> B.OrdMap<Nat, Node<T>>:
  set_next(T, set_prev(T, put(T, nodes, n, N{x, a, b}), b, Some{n}), a, Some{n})

# Drop node h whose neighbours are a and b, linking them to each other.
def unlink(-T: Data, nodes: B.OrdMap<Nat, Node<T>>, +h: Nat, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>) -> B.OrdMap<Nat, Node<T>>:
  set_next(T, set_prev(T, drop(T, nodes, h), b, a), a, b)

# End pointer after linking n next to neighbour a (None: n becomes the end).
def end_link(a: Maybe<&2, Nat>, +n: Nat, e: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      Some{n}
    case Some{x}:
      e

# End pointer after unlinking a node whose neighbour on that side is a.
def end_unlink(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, e: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      b
    case Some{x}:
      e

def insert_between(-T: Data, +tag: Nat, +fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, Node<T>>, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, x: T) -> DList<T> & E.Handle:
  (DL{tag, 1n+fresh, 1n+count, end_link(a, fresh, head), end_link(b, fresh, tail), link(T, nodes, a, b, fresh, x)}, E.H{tag, fresh})

def length(-T: Data, s: DList<T>) -> Nat:
  match s:
    case DL{tag, fresh, count, head, tail, nodes}:
      count

def push_front(-T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  match s:
    case DL{+tag, +fresh, count, +head, tail, nodes}:
      insert_between(T, tag, fresh, count, head, tail, nodes, None{}, head, x)

def push_back(-T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  match s:
    case DL{+tag, +fresh, count, head, +tail, nodes}:
      insert_between(T, tag, fresh, count, head, tail, nodes, tail, None{}, x)

def done_handle(-T: Data, r: DList<T> & E.Handle) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  (s, h) = r
  (s, Done{h})

def insert_checked(-T: Data, after: Bool, same: Bool, m: Maybe<&2, Node<T>>, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, Node<T>>, +i: Nat, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match after same m:
    case _ False{} _:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.ForeignHandle{}})
    case _ True{} None{}:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.StaleHandle{}})
    case False{} True{} Some{N{v, p, n}}:
      done_handle(T, insert_between(T, tag, fresh, count, head, tail, nodes, p, Some{i}, x))
    case True{} True{} Some{N{v, p, n}}:
      done_handle(T, insert_between(T, tag, fresh, count, head, tail, nodes, Some{i}, n, x))

# Insert x immediately before the element of h.
def insert_before(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match s h:
    case DL{+tag, +fresh, +count, +head, +tail, +nodes} E.H{+l, +i}:
      insert_checked(T, False{}, Nat.is_eq(l, tag), node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x)

# Insert x immediately after the element of h.
def insert_after(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match s h:
    case DL{+tag, +fresh, +count, +head, +tail, +nodes} E.H{+l, +i}:
      insert_checked(T, True{}, Nat.is_eq(l, tag), node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x)

def remove_checked(-T: Data, same: Bool, m: Maybe<&2, Node<T>>, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, Node<T>>, +i: Nat) -> DList<T> & Result<&2, &2, E.Error, T>:
  match same m:
    case False{} _:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.ForeignHandle{}})
    case True{} None{}:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.StaleHandle{}})
    case True{} Some{N{v, +p, +n}}:
      (DL{tag, fresh, Nat.sub(count, 1n), end_unlink(p, n, head), end_unlink(n, p, tail), unlink(T, nodes, i, p, n)}, Done{v})

# Remove the element of h, returning its value.
def remove(-T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>:
  match s h:
    case DL{+tag, +fresh, +count, +head, +tail, +nodes} E.H{+l, +i}:
      remove_checked(T, Nat.is_eq(l, tag), node(T, nodes, i), tag, fresh, count, head, tail, nodes, i)

def value(-T: Data, same: Bool, m: Maybe<&2, Node<T>>) -> Result<&2, &2, E.Error, T>:
  match same m:
    case False{} _:
      Fail{E.ForeignHandle{}}
    case True{} None{}:
      Fail{E.StaleHandle{}}
    case True{} Some{N{v, p, n}}:
      Done{v}

def get(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, T>:
  match s h:
    case DL{+tag, fresh, count, head, tail, +nodes} E.H{+l, +i}:
      value(T, Nat.is_eq(l, tag), node(T, nodes, i))

def set_checked(-T: Data, same: Bool, m: Maybe<&2, Node<T>>, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, Node<T>>, +i: Nat, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  match same m:
    case False{} _:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.ForeignHandle{}})
    case True{} None{}:
      (DL{tag, fresh, count, head, tail, nodes}, Fail{E.StaleHandle{}})
    case True{} Some{N{v, p, n}}:
      (DL{tag, fresh, count, head, tail, put(T, nodes, i, N{x, p, n})}, Done{Unit{}})

# Replace the value of the element of h.
def set(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  match s h:
    case DL{+tag, +fresh, +count, +head, +tail, +nodes} E.H{+l, +i}:
      set_checked(T, Nat.is_eq(l, tag), node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x)

def handle(+tag: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, E.Handle>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{E.H{tag, i}}

def nbr(-T: Data, after: Bool, same: Bool, m: Maybe<&2, Node<T>>, +tag: Nat) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match after same m:
    case _ False{} _:
      Fail{E.ForeignHandle{}}
    case _ True{} None{}:
      Fail{E.StaleHandle{}}
    case True{} True{} Some{N{v, p, n}}:
      Done{handle(tag, n)}
    case False{} True{} Some{N{v, p, n}}:
      Done{handle(tag, p)}

# Handle of the following element (None at the end).
def next(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match s h:
    case DL{+tag, fresh, count, head, tail, +nodes} E.H{+l, +i}:
      nbr(T, True{}, Nat.is_eq(l, tag), node(T, nodes, i), tag)

# Handle of the preceding element (None at the start).
def prev(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match s h:
    case DL{+tag, fresh, count, head, tail, +nodes} E.H{+l, +i}:
      nbr(T, False{}, Nat.is_eq(l, tag), node(T, nodes, i), tag)

# Values from head, following next links (fuel = element count).
def walkv(-T: Data, fuel: Nat, +nodes: B.OrdMap<Nat, Node<T>>, m: Maybe<&2, Node<T>>) -> List<&2, T>:
  match fuel m:
    case 0n _:
      Nil{}
    case 1n+f None{}:
      Nil{}
    case 1n+f Some{N{v, p, n}}:
      Con{v, walkv(T, f, nodes, nodeM(T, nodes, n))}

def to_list(-T: Data, s: DList<T>) -> List<&2, T>:
  match s:
    case DL{tag, fresh, count, head, tail, +nodes}:
      walkv(T, count, nodes, nodeM(T, nodes, head))

# ---- trace runner ----

def obs_handle(-T: Data, r: DList<T> & E.Handle) -> DList<T> & E.Obs<T>:
  (s, h) = r
  (s, E.OHandle{h})

def obs_insert(-T: Data, r: DList<T> & Result<&2, &2, E.Error, E.Handle>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OInsert{x})

def obs_val(-T: Data, r: DList<T> & Result<&2, &2, E.Error, T>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OVal{x})

def obs_unit(-T: Data, r: DList<T> & Result<&2, &2, E.Error, Unit>) -> DList<T> & E.Obs<T>:
  (s, x) = r
  (s, E.OUnit{x})

def step(-T: Data, +s: DList<T>, op: E.Op<T>) -> DList<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (s, E.ONat{length(T, s)})
    case E.PushFront{x}:
      obs_handle(T, push_front(T, s, x))
    case E.PushBack{x}:
      obs_handle(T, push_back(T, s, x))
    case E.InsertBefore{h, x}:
      obs_insert(T, insert_before(T, s, h, x))
    case E.InsertAfter{h, x}:
      obs_insert(T, insert_after(T, s, h, x))
    case E.Remove{h}:
      obs_val(T, remove(T, s, h))
    case E.Get{h}:
      (s, E.OVal{get(T, s, h)})
    case E.Set{h, x}:
      obs_unit(T, set(T, s, h, x))
    case E.Next{h}:
      (s, E.ONbr{next(T, s, h)})
    case E.Prev{h}:
      (s, E.ONbr{prev(T, s, h)})
    case E.ToList{}:
      (s, E.OList{to_list(T, s)})

def record(-T: Data, acc: List<&2, E.Obs<T>>, r: DList<T> & E.Obs<T>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(-T: Data, op: E.Op<T>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  record(T, acc, step(T, s, op))

def run_acc(-T: Data, ops: List<&2, E.Op<T>>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(T, rest, step_acc(T, op, st))

def finish(-T: Data, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs<T>, acc))

def run(-T: Data, ops: List<&2, E.Op<T>>, s: DList<T>) -> DList<T> & List<&2, E.Obs<T>>:
  finish(T, run_acc(T, ops, (s, Nil{})))
