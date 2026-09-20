import Base
import ./common.bend as C
import ./u32seq.bend as Q
import ../types/segment_tree.bend as E

# Independent model: the sequence of n U32 values; sums and additions wrap
# modulo 2^32. Nothing here refers to trees or lazy tags.

def new(n: Nat) -> List<&2, U32>:
  Q.zeros(n)

def from_list(xs: List<&2, U32>) -> List<&2, U32>:
  xs

def item(x: Maybe<&2, U32>) -> Result<&2, &2, E.Error, U32>:
  match x:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{v}:
      Done{v}

def assign(x: Maybe<&2, U32>, +xs: List<&2, U32>, i: Nat, v: U32) -> List<&2, U32> & E.Obs:
  match x:
    case None{}:
      (xs, E.OUnit{Fail{E.IndexOutOfRange{}}})
    case Some{y}:
      (C.update(U32, xs, i, v), E.OUnit{Done{Unit{}}})

def query_if(ok: Bool, xs: List<&2, U32>, +l: Nat, r: Nat) -> Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      Done{Q.sum(Q.slice(xs, l, r))}
    case False{}:
      Fail{E.InvalidRange{}}

# Values [0, l), then [l, r) each increased by v, then [r, n).
def added(+xs: List<&2, U32>, +l: Nat, +r: Nat, +v: U32) -> List<&2, U32>:
  C.append(U32, C.take(U32, xs, l), C.append(U32, Q.add_each(Q.slice(xs, l, r), v), C.drop(U32, xs, r)))

def add_if(ok: Bool, +xs: List<&2, U32>, +l: Nat, +r: Nat, +v: U32) -> List<&2, U32> & E.Obs:
  match ok:
    case True{}:
      (added(xs, l, r, v), E.OUnit{Done{Unit{}}})
    case False{}:
      (xs, E.OUnit{Fail{E.InvalidRange{}}})

def step(+xs: List<&2, U32>, op: E.Op) -> List<&2, U32> & E.Obs:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(U32, xs)})
    case E.Get{+i}:
      (xs, E.OItem{item(C.nth(U32, xs, i))})
    case E.Set{+i, v}:
      assign(C.nth(U32, xs, i), xs, i, v)
    case E.RangeQuery{+l, +r}:
      (xs, E.OItem{query_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, C.length(U32, xs))), xs, l, r)})
    case E.RangeAdd{+l, +r, +v}:
      add_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, C.length(U32, xs))), xs, l, r, v)

def cons_obs(o: E.Obs, r: List<&2, U32> & List<&2, E.Obs>) -> List<&2, U32> & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +xs: List<&2, U32>) -> List<&2, U32> & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(List<&2, U32>, E.Obs, step(xs, op)), run(rest, Pair.fst(List<&2, U32>, E.Obs, step(xs, op))))
