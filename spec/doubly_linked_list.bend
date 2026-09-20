import Base
import ./common.bend as SC
import ../types/doubly_linked_list.bend as E

# Independent model: the sequence of (id, value) items in list order, the
# next fresh id, and the list's tag. A handle is valid for a list when its
# tag is the list's tag (else ForeignHandle) and its id is present (else
# StaleHandle: never issued, or already removed). Ids are never reused.

type Model<-T: Data> is Data:
  DM{tag: Nat, fresh: Nat, items: List<&2, E.Item<T>>}

def new(-T: Data, tag: Nat) -> Model<T>:
  DM{tag, 0n, Nil{}}

def is_id(-T: Data, +i: Nat, it: E.Item<T>) -> Bool:
  match it:
    case E.Item{j, v}:
      Nat.is_eq(j, i)

def getv_at(-T: Data, b: Bool, v: T, rest: Maybe<&2, T>) -> Maybe<&2, T>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      rest

def getv(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat) -> Maybe<&2, T>:
  match xs:
    case Nil{}:
      None{}
    case Con{E.Item{j, v}, t}:
      getv_at(T, Nat.is_eq(j, i), v, getv(T, t, i))

def pick(-T: Data, b: Bool, here: List<&2, E.Item<T>>, there: List<&2, E.Item<T>>) -> List<&2, E.Item<T>>:
  match b:
    case True{}:
      here
    case False{}:
      there

# Insert it before / after the item with id i.
def ins_before(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      pick(T, Nat.is_eq(j, i), Con{it, Con{E.Item{j, v}, t}}, Con{E.Item{j, v}, ins_before(T, t, i, it)})

def ins_after(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      pick(T, Nat.is_eq(j, i), Con{E.Item{j, v}, Con{it, t}}, Con{E.Item{j, v}, ins_after(T, t, i, it)})

def del(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      pick(T, Nat.is_eq(j, i), t, Con{E.Item{j, v}, del(T, t, i)})

def setv(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat, +x: T) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      pick(T, Nat.is_eq(j, i), Con{E.Item{j, x}, t}, Con{E.Item{j, v}, setv(T, t, i, x)})

def first_id(-T: Data, xs: List<&2, E.Item<T>>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{E.Item{j, v}, t}:
      Some{j}

def pickm(b: Bool, here: Maybe<&2, Nat>, there: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      here
    case False{}:
      there

# Id of the item after / before the item with id i.
def next_of(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{E.Item{+j, v}, +t}:
      pickm(Nat.is_eq(j, i), first_id(T, t), next_of(T, t, i))

def prev_of(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat, p: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{E.Item{+j, v}, t}:
      pickm(Nat.is_eq(j, i), p, prev_of(T, t, i, Some{j}))

def vals(-T: Data, xs: List<&2, E.Item<T>>) -> List<&2, T>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{j, v}, t}:
      Con{v, vals(T, t)}

def handle(+tag: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, E.Handle>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{E.H{tag, i}}

# Validity: the tag check first, then presence.
def check(-T: Data, same: Bool, m: Maybe<&2, T>) -> Maybe<&2, E.Error>:
  match same m:
    case False{} _:
      Some{E.ForeignHandle{}}
    case True{} None{}:
      Some{E.StaleHandle{}}
    case True{} Some{v}:
      None{}

def insert_at(-T: Data, c: Maybe<&2, E.Error>, +tag: Nat, +fresh: Nat, +xs: List<&2, E.Item<T>>, ys: List<&2, E.Item<T>>) -> Model<T> & E.Obs<T>:
  match c:
    case Some{e}:
      (DM{tag, fresh, xs}, E.OInsert{Fail{e}})
    case None{}:
      (DM{tag, 1n+fresh, ys}, E.OInsert{Done{E.H{tag, fresh}}})

def value(-T: Data, same: Bool, m: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match same m:
    case False{} _:
      Fail{E.ForeignHandle{}}
    case True{} None{}:
      Fail{E.StaleHandle{}}
    case True{} Some{v}:
      Done{v}

def remove_at(-T: Data, same: Bool, m: Maybe<&2, T>, +tag: Nat, +fresh: Nat, +xs: List<&2, E.Item<T>>, +i: Nat) -> Model<T> & E.Obs<T>:
  match same m:
    case False{} _:
      (DM{tag, fresh, xs}, E.OVal{Fail{E.ForeignHandle{}}})
    case True{} None{}:
      (DM{tag, fresh, xs}, E.OVal{Fail{E.StaleHandle{}}})
    case True{} Some{v}:
      (DM{tag, fresh, del(T, xs, i)}, E.OVal{Done{v}})

def set_at(-T: Data, c: Maybe<&2, E.Error>, +tag: Nat, +fresh: Nat, +xs: List<&2, E.Item<T>>, +i: Nat, +x: T) -> Model<T> & E.Obs<T>:
  match c:
    case Some{e}:
      (DM{tag, fresh, xs}, E.OUnit{Fail{e}})
    case None{}:
      (DM{tag, fresh, setv(T, xs, i, x)}, E.OUnit{Done{Unit{}}})

def nbr(c: Maybe<&2, E.Error>, r: Maybe<&2, E.Handle>) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match c:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{r}

def step(-T: Data, +m: Model<T>, op: E.Op<T>) -> Model<T> & E.Obs<T>:
  match m op:
    case DM{+tag, +fresh, +xs} E.Length{}:
      (DM{tag, fresh, xs}, E.ONat{SC.length(E.Item<T>, xs)})
    case DM{+tag, +fresh, +xs} E.PushFront{+x}:
      (DM{tag, 1n+fresh, Con{E.Item{fresh, x}, xs}}, E.OHandle{E.H{tag, fresh}})
    case DM{+tag, +fresh, +xs} E.PushBack{+x}:
      (DM{tag, 1n+fresh, SC.append(E.Item<T>, xs, Con{E.Item{fresh, x}, Nil{}})}, E.OHandle{E.H{tag, fresh}})
    case DM{+tag, +fresh, +xs} E.InsertBefore{E.H{+l, +i}, +x}:
      insert_at(T, check(T, Nat.is_eq(l, tag), getv(T, xs, i)), tag, fresh, xs, ins_before(T, xs, i, E.Item{fresh, x}))
    case DM{+tag, +fresh, +xs} E.InsertAfter{E.H{+l, +i}, +x}:
      insert_at(T, check(T, Nat.is_eq(l, tag), getv(T, xs, i)), tag, fresh, xs, ins_after(T, xs, i, E.Item{fresh, x}))
    case DM{+tag, +fresh, +xs} E.Remove{E.H{+l, +i}}:
      remove_at(T, Nat.is_eq(l, tag), getv(T, xs, i), tag, fresh, xs, i)
    case DM{+tag, +fresh, +xs} E.Get{E.H{+l, +i}}:
      (DM{tag, fresh, xs}, E.OVal{value(T, Nat.is_eq(l, tag), getv(T, xs, i))})
    case DM{+tag, +fresh, +xs} E.Set{E.H{+l, +i}, +x}:
      set_at(T, check(T, Nat.is_eq(l, tag), getv(T, xs, i)), tag, fresh, xs, i, x)
    case DM{+tag, +fresh, +xs} E.Next{E.H{+l, +i}}:
      (DM{tag, fresh, xs}, E.ONbr{nbr(check(T, Nat.is_eq(l, tag), getv(T, xs, i)), handle(tag, next_of(T, xs, i)))})
    case DM{+tag, +fresh, +xs} E.Prev{E.H{+l, +i}}:
      (DM{tag, fresh, xs}, E.ONbr{nbr(check(T, Nat.is_eq(l, tag), getv(T, xs, i)), handle(tag, prev_of(T, xs, i, None{})))})
    case DM{+tag, +fresh, +xs} E.ToList{}:
      (DM{tag, fresh, xs}, E.OList{vals(T, xs)})

def cons_obs(-T: Data, o: E.Obs<T>, r: Model<T> & List<&2, E.Obs<T>>) -> Model<T> & List<&2, E.Obs<T>>:
  (m, os) = r
  (m, Con{o, os})

def run(-T: Data, ops: List<&2, E.Op<T>>, +m: Model<T>) -> Model<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      (m, Nil{})
    case Con{+op, rest}:
      cons_obs(T, Pair.snd(Model<T>, E.Obs<T>, step(T, m, op)), run(T, rest, Pair.fst(Model<T>, E.Obs<T>, step(T, m, op))))
