import Base
import ./common.bend as C
import ./u32seq.bend as Q
import ../types/fenwick_tree.bend as E

# Independent model: the sequence of n U32 values. Sums wrap modulo 2^32.
# Nothing here refers to trees or partial sums.

def new(n: Nat) -> List<&2, U32>:
  Q.zeros(n)

def from_list(xs: List<&2, U32>) -> List<&2, U32>:
  xs

def add_at(x: Maybe<&2, U32>, +xs: List<&2, U32>, i: Nat, v: U32) -> List<&2, U32> & E.Obs:
  match x:
    case None{}:
      (xs, E.OUnit{Fail{E.IndexOutOfRange{}}})
    case Some{y}:
      (C.update(U32, xs, i, U32.add(y, v)), E.OUnit{Done{Unit{}}})

def prefix_if(ok: Bool, xs: List<&2, U32>, e: Nat) -> Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      Done{Q.sum(C.take(U32, xs, e))}
    case False{}:
      Fail{E.InvalidRange{}}

def range_if(ok: Bool, xs: List<&2, U32>, +l: Nat, r: Nat) -> Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      Done{Q.sum(Q.slice(xs, l, r))}
    case False{}:
      Fail{E.InvalidRange{}}

def step(+xs: List<&2, U32>, op: E.Op) -> List<&2, U32> & E.Obs:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(U32, xs)})
    case E.Add{+i, v}:
      add_at(C.nth(U32, xs, i), xs, i, v)
    case E.PrefixSum{+e}:
      (xs, E.OSum{prefix_if(Nat.is_le(e, C.length(U32, xs)), xs, e)})
    case E.RangeSum{+l, +r}:
      (xs, E.OSum{range_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, C.length(U32, xs))), xs, l, r)})

def cons_obs(o: E.Obs, r: List<&2, U32> & List<&2, E.Obs>) -> List<&2, U32> & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +xs: List<&2, U32>) -> List<&2, U32> & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(List<&2, U32>, E.Obs, step(xs, op)), run(rest, Pair.fst(List<&2, U32>, E.Obs, step(xs, op))))
