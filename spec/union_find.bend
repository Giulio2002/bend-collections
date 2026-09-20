import Base
import ./common.bend as C
import ../types/union_find.bend as E

# Independent model: a partition of {0, ..., n-1} given by a labelling. The
# list holds, for every element, the representative of its class; the
# representative of a class is one of its members. Joining two classes keeps
# the representative of the larger class (ties: the class of the first
# argument) and relabels the other class.

def iota(n: Nat, +off: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{off, iota(k, 1n+off)}

# Every element starts in its own class.
def new(n: Nat) -> List<&2, Nat>:
  iota(n, 0n)

def eq_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Size of the class labelled v.
def count_eq(xs: List<&2, Nat>, +v: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(eq_bit(Nat.is_eq(h, v)), count_eq(t, v))

# Number of classes: elements that are their own representative (xs[i] == off+i).
def fixed(xs: List<&2, Nat>, +off: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(eq_bit(Nat.is_eq(h, off)), fixed(t, 1n+off))

def swap_label(same: Bool, +to: Nat, h: Nat) -> Nat:
  match same:
    case True{}:
      to
    case False{}:
      h

# Move every element of class `from` into class `to`.
def relabel(xs: List<&2, Nat>, +from: Nat, +to: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{swap_label(Nat.is_eq(h, from), to, h), relabel(t, from, to)}

def label(x: Maybe<&2, Nat>) -> Result<&2, &2, E.Error, Nat>:
  match x:
    case None{}:
      Fail{E.OutOfRange{}}
    case Some{v}:
      Done{v}

def class_size(x: Maybe<&2, Nat>, xs: List<&2, Nat>) -> Result<&2, &2, E.Error, Nat>:
  match x:
    case None{}:
      Fail{E.OutOfRange{}}
    case Some{v}:
      Done{count_eq(xs, v)}

def same_class(x: Maybe<&2, Nat>, y: Maybe<&2, Nat>) -> Result<&2, &2, E.Error, Bool>:
  match x y:
    case Some{a} Some{b}:
      Done{Nat.is_eq(a, b)}
    case _ _:
      Fail{E.OutOfRange{}}

def join_keep(keep_a: Bool, +xs: List<&2, Nat>, +la: Nat, +lb: Nat) -> List<&2, Nat>:
  match keep_a:
    case True{}:
      relabel(xs, lb, la)
    case False{}:
      relabel(xs, la, lb)

def join_labels(same: Bool, +xs: List<&2, Nat>, +la: Nat, +lb: Nat) -> List<&2, Nat> & E.Obs:
  match same:
    case True{}:
      (xs, E.OBool{Done{False{}}})
    case False{}:
      (join_keep(Nat.is_le(count_eq(xs, lb), count_eq(xs, la)), xs, la, lb), E.OBool{Done{True{}}})

def join(x: Maybe<&2, Nat>, y: Maybe<&2, Nat>, +xs: List<&2, Nat>) -> List<&2, Nat> & E.Obs:
  match x y:
    case Some{+la} Some{+lb}:
      join_labels(Nat.is_eq(la, lb), xs, la, lb)
    case _ _:
      (xs, E.OBool{Fail{E.OutOfRange{}}})

def step(+xs: List<&2, Nat>, op: E.Op) -> List<&2, Nat> & E.Obs:
  match op:
    case E.Find{+x}:
      (xs, E.OItem{label(C.nth(Nat, xs, x))})
    case E.Union{+a, +b}:
      join(C.nth(Nat, xs, a), C.nth(Nat, xs, b), xs)
    case E.Connected{+a, +b}:
      (xs, E.OBool{same_class(C.nth(Nat, xs, a), C.nth(Nat, xs, b))})
    case E.ComponentSize{+x}:
      (xs, E.OItem{class_size(C.nth(Nat, xs, x), xs)})
    case E.ComponentCount{}:
      (xs, E.ONat{fixed(xs, 0n)})

def cons_obs(o: E.Obs, r: List<&2, Nat> & List<&2, E.Obs>) -> List<&2, Nat> & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +xs: List<&2, Nat>) -> List<&2, Nat> & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(List<&2, Nat>, E.Obs, step(xs, op)), run(rest, Pair.fst(List<&2, Nat>, E.Obs, step(xs, op))))
