import Base
import ./common.bend as C
import ../../src/containers/types/doubly_linked_list.bend as E

# Independent model of the doubly linked list with generational handles.
#
# A list is its elements' ids in order, and for every id ever issued its value
# (None once removed) and its generation. Removed ids are kept on a stack and
# reissued last-removed first; an id whose generation reached 2^32 - 1 is
# retired instead (never reissued). A new id, when none is free, is the next
# one, at generation 0. A handle names the list's tag, an id and a
# generation: it is foreign when the tag differs, and stale when its id is
# not live or its generation is not the id's current one.
#
# Nothing here refers to the arenas, links or free chain of the
# implementation.

type DS<-T: Data> is Data:
  DS{tag: U32, order: List<&2, Nat>, vals: List<&2, Maybe<&2, T>>, gens: List<&2, U32>, free: List<&2, Nat>}

def pick_list(+b: Bool, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      xs
    case False{}:
      ys

def pick_maybe(+b: Bool, x: Maybe<&2, Nat>, y: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

def cons_some(-T: Data, m: Maybe<&2, T>, xs: List<&2, T>) -> List<&2, T>:
  match m:
    case None{}:
      xs
    case Some{v}:
      Con{v, xs}

def maybe_done(-T: Data, e: E.Error, m: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match m:
    case None{}:
      Fail{e}
    case Some{v}:
      Done{v}

def gen_of(+gens: List<&2, U32>, +i: Nat) -> U32:
  match gens i:
    case Nil{} _:
      0
    case Con{g, t} 0n:
      g
    case Con{g, t} 1n+p:
      gen_of(t, p)

def val_of(-T: Data, +vals: List<&2, Maybe<&2, T>>, +i: Nat) -> Maybe<&2, T>:
  match vals i:
    case Nil{} _:
      None{}
    case Con{v, t} 0n:
      v
    case Con{v, t} 1n+p:
      val_of(T, t, p)

def handle(+tag: U32, +gens: List<&2, U32>, +i: Nat) -> E.Handle:
  E.H{tag, U32.from_nat(i), gen_of(gens, i)}

# ---- validity ----

def live_gen(-T: Data, m: Maybe<&2, T>, +same: Bool) -> Maybe<&2, E.Error>:
  match m same:
    case None{} _:
      Some{E.StaleHandle{}}
    case Some{v} True{}:
      None{}
    case Some{v} False{}:
      Some{E.StaleHandle{}}

def valid_own(-T: Data, +vals: List<&2, Maybe<&2, T>>, +gens: List<&2, U32>, +i: Nat, +g: U32, mine: Bool) -> Maybe<&2, E.Error>:
  match mine:
    case False{}:
      Some{E.ForeignHandle{}}
    case True{}:
      live_gen(T, val_of(T, vals, i), U32.is_eq(gen_of(gens, i), g))

# None when h names a live element of the list at its current generation
def validate(-T: Data, +s: DS<T>, +h: E.Handle) -> Maybe<&2, E.Error>:
  match s h:
    case DS{+tag, +order, +vals, +gens, +free} E.H{+owner, +id, +g}:
      valid_own(T, vals, gens, U32.to_nat(id), g, U32.is_eq(owner, tag))

# ---- positions in the order ----

def ins_before(xs: List<&2, Nat>, +i: Nat, +n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      pick_list(Nat.is_eq(x, i), Con{n, Con{x, t}}, Con{x, ins_before(t, i, n)})

def ins_after(xs: List<&2, Nat>, +i: Nat, +n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      pick_list(Nat.is_eq(x, i), Con{x, Con{n, t}}, Con{x, ins_after(t, i, n)})

def delete(xs: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      pick_list(Nat.is_eq(x, i), t, Con{x, delete(t, i)})

def first(xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      Some{x}

# the element after i
def after(xs: List<&2, Nat>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, +t}:
      pick_maybe(Nat.is_eq(x, i), first(t), after(t, i))

# the element before i (p: the element before the list)
def before(xs: List<&2, Nat>, +i: Nat, p: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, +t}:
      pick_maybe(Nat.is_eq(x, i), p, before(t, i, Some{x}))

def values(-T: Data, +vals: List<&2, Maybe<&2, T>>, xs: List<&2, Nat>) -> List<&2, T>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      cons_some(T, val_of(T, vals, x), values(T, vals, t))

# ---- issuing an id ----

# the id a new element takes, the list with the id reserved
def alloc(-T: Data, s: DS<T>) -> DS<T> & Nat:
  match s:
    case DS{+tag, +order, +vals, +gens, free}:
      match free:
        case Con{+i, rest}:
          (DS{tag, order, vals, gens, rest}, i)
        case Nil{}:
          (DS{tag, order, C.snoc(Maybe<&2, T>, vals, None{}), C.snoc(U32, gens, 0), Nil{}}, C.length(Maybe<&2, T>, vals))

# where a new element goes
type Pos is Data:
  PFront{}
  PBack{}
  PBefore{i: Nat}
  PAfter{i: Nat}

def place_order(pos: Pos, xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match pos:
    case PFront{}:
      Con{n, xs}
    case PBack{}:
      C.snoc(Nat, xs, n)
    case PBefore{+i}:
      ins_before(xs, i, n)
    case PAfter{+i}:
      ins_after(xs, i, n)

# store x at the reserved id n and place n in the order
def place(-T: Data, s: DS<T>, +n: Nat, x: T, pos: Pos) -> DS<T> & E.Handle:
  match s:
    case DS{+tag, order, +vals, +gens, free}:
      (DS{tag, place_order(pos, order, n), C.update(Maybe<&2, T>, vals, n, Some{x}), gens, free}, handle(tag, gens, n))

def inserted(-T: Data, r: DS<T> & Nat, x: T, pos: Pos) -> DS<T> & E.Handle:
  match r:
    case Tuple{s, +n}:
      place(T, s, n, x, pos)

def push_front(-T: Data, s: DS<T>, x: T) -> DS<T> & E.Handle:
  inserted(T, alloc(T, s), x, PFront{})

def push_back(-T: Data, s: DS<T>, x: T) -> DS<T> & E.Handle:
  inserted(T, alloc(T, s), x, PBack{})

# ---- removal ----

def retire(+gens: List<&2, U32>, +i: Nat, +free: List<&2, Nat>, +g: U32, exhausted: Bool) -> List<&2, U32> & List<&2, Nat>:
  match exhausted:
    case True{}:
      (gens, free)
    case False{}:
      (C.update(U32, gens, i, U32.inc(g)), Con{i, free})

def removed(-T: Data, +tag: U32, +order: List<&2, Nat>, +vals: List<&2, Maybe<&2, T>>, +i: Nat, +v: T, r: List<&2, U32> & List<&2, Nat>) -> DS<T> & E.Obs<T>:
  match r:
    case Tuple{gens, free}:
      (DS{tag, delete(order, i), C.update(Maybe<&2, T>, vals, i, None{}), gens, free}, E.OVal{Done{v}})

def remove_m(-T: Data, +tag: U32, +order: List<&2, Nat>, +vals: List<&2, Maybe<&2, T>>, +gens: List<&2, U32>, +free: List<&2, Nat>, +i: Nat, m: Maybe<&2, T>) -> DS<T> & E.Obs<T>:
  match m:
    case Some{+v}:
      removed(T, tag, order, vals, i, v, retire(gens, i, free, gen_of(gens, i), U32.is_eq(gen_of(gens, i), 4294967295)))
    case None{}:
      (DS{tag, order, vals, gens, free}, E.OVal{Fail{E.StaleHandle{}}})

def remove_live(-T: Data, s: DS<T>, +i: Nat) -> DS<T> & E.Obs<T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      remove_m(T, tag, order, vals, gens, free, i, val_of(T, vals, i))

# ---- one operation on a valid handle ----

def get_live(-T: Data, s: DS<T>, +i: Nat) -> DS<T> & E.Obs<T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      (DS{tag, order, vals, gens, free}, E.OVal{maybe_done(T, E.StaleHandle{}, val_of(T, vals, i))})

def set_live(-T: Data, s: DS<T>, +i: Nat, x: T) -> DS<T> & E.Obs<T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      (DS{tag, order, C.update(Maybe<&2, T>, vals, i, Some{x}), gens, free}, E.OUnit{Done{Unit{}}})

def nbr(+tag: U32, +gens: List<&2, U32>, m: Maybe<&2, Nat>) -> Maybe<&2, E.Handle>:
  match m:
    case None{}:
      None{}
    case Some{+j}:
      Some{handle(tag, gens, j)}

def next_live(-T: Data, s: DS<T>, +i: Nat) -> DS<T> & E.Obs<T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      (DS{tag, order, vals, gens, free}, E.ONbr{Done{nbr(tag, gens, after(order, i))}})

def prev_live(-T: Data, s: DS<T>, +i: Nat) -> DS<T> & E.Obs<T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      (DS{tag, order, vals, gens, free}, E.ONbr{Done{nbr(tag, gens, before(order, i, None{}))}})

def ins_obs(-T: Data, r: DS<T> & E.Handle) -> DS<T> & E.Obs<T>:
  match r:
    case Tuple{s, h}:
      (s, E.OInsert{Done{h}})

def live_op(-T: Data, s: DS<T>, +op: E.Op<T>, +i: Nat) -> DS<T> & E.Obs<T>:
  match op:
    case E.InsertBefore{h, x}:
      ins_obs(T, inserted(T, alloc(T, s), x, PBefore{i}))
    case E.InsertAfter{h, x}:
      ins_obs(T, inserted(T, alloc(T, s), x, PAfter{i}))
    case E.Remove{h}:
      remove_live(T, s, i)
    case E.Get{h}:
      get_live(T, s, i)
    case E.Set{h, x}:
      set_live(T, s, i, x)
    case E.Next{h}:
      next_live(T, s, i)
    case E.Prev{h}:
      prev_live(T, s, i)
    case E.Length{}:
      (s, E.ONat{0n})
    case E.PushFront{x}:
      (s, E.ONat{0n})
    case E.PushBack{x}:
      (s, E.ONat{0n})
    case E.ToList{}:
      (s, E.ONat{0n})

# the observation of op failing with e (the list is unchanged)
def failed(-T: Data, op: E.Op<T>, e: E.Error) -> E.Obs<T>:
  match op:
    case E.InsertBefore{h, x}:
      E.OInsert{Fail{e}}
    case E.InsertAfter{h, x}:
      E.OInsert{Fail{e}}
    case E.Remove{h}:
      E.OVal{Fail{e}}
    case E.Get{h}:
      E.OVal{Fail{e}}
    case E.Set{h, x}:
      E.OUnit{Fail{e}}
    case E.Next{h}:
      E.ONbr{Fail{e}}
    case E.Prev{h}:
      E.ONbr{Fail{e}}
    case E.Length{}:
      E.ONat{0n}
    case E.PushFront{x}:
      E.ONat{0n}
    case E.PushBack{x}:
      E.ONat{0n}
    case E.ToList{}:
      E.ONat{0n}

def handle_id(+h: E.Handle) -> Nat:
  match h:
    case E.H{+owner, +id, +g}:
      U32.to_nat(id)

def checked(-T: Data, +s: DS<T>, +op: E.Op<T>, +h: E.Handle, m: Maybe<&2, E.Error>) -> DS<T> & E.Obs<T>:
  match m:
    case Some{e}:
      (s, failed(T, op, e))
    case None{}:
      live_op(T, s, op, handle_id(h))

def with_handle(-T: Data, +s: DS<T>, +op: E.Op<T>, +h: E.Handle) -> DS<T> & E.Obs<T>:
  checked(T, s, op, h, validate(T, s, h))

def len_of(-T: Data, s: DS<T>) -> Nat:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      C.length(Nat, order)

def list_of(-T: Data, s: DS<T>) -> List<&2, T>:
  match s:
    case DS{+tag, +order, +vals, +gens, +free}:
      values(T, vals, order)

def pushed(-T: Data, r: DS<T> & E.Handle) -> DS<T> & E.Obs<T>:
  match r:
    case Tuple{s, h}:
      (s, E.OHandle{h})

def step(-T: Data, +s: DS<T>, op: E.Op<T>) -> DS<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (s, E.ONat{len_of(T, s)})
    case E.PushFront{x}:
      pushed(T, push_front(T, s, x))
    case E.PushBack{x}:
      pushed(T, push_back(T, s, x))
    case E.InsertBefore{+h, +x}:
      with_handle(T, s, E.InsertBefore{h, x}, h)
    case E.InsertAfter{+h, +x}:
      with_handle(T, s, E.InsertAfter{h, x}, h)
    case E.Remove{+h}:
      with_handle(T, s, E.Remove{h}, h)
    case E.Get{+h}:
      with_handle(T, s, E.Get{h}, h)
    case E.Set{+h, +x}:
      with_handle(T, s, E.Set{h, x}, h)
    case E.Next{+h}:
      with_handle(T, s, E.Next{h}, h)
    case E.Prev{+h}:
      with_handle(T, s, E.Prev{h}, h)
    case E.ToList{}:
      (s, E.OList{list_of(T, s)})

def empty(-T: Data, +tag: U32) -> DS<T>:
  DS{tag, Nil{}, Nil{}, Nil{}, Nil{}}

def cons_obs(-T: Data, o: E.Obs<T>, r: DS<T> & List<&2, E.Obs<T>>) -> DS<T> & List<&2, E.Obs<T>>:
  match r:
    case Tuple{m, os}:
      (m, Con{o, os})

def run(-T: Data, ops: List<&2, E.Op<T>>, +s: DS<T>) -> DS<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      (s, Nil{})
    case Con{+op, rest}:
      cons_obs(T, Pair.snd(DS<T>, E.Obs<T>, step(T, s, op)), run(T, rest, Pair.fst(DS<T>, E.Obs<T>, step(T, s, op))))
