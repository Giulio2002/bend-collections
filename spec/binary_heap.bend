import Base
import ./common.bend as C
import ../types/binary_heap.bend as E

# Independent model: a priority queue is the finite multiset of its elements,
# represented canonically as the list sorted ascending by the comparator
# (insertion sort). Equal-comparing elements are identical under the order
# laws, so the sorted list is unique for each multiset. Nothing here refers
# to trees.

def le(~A: Data, ~cmp: A -> A -> Cmp, x: A, y: A) -> Bool:
  Cmp.is_le(cmp(x, y))

# Insert into a sorted list, before the first element not smaller than x.
def ins(~A: Data, ~cmp: A -> A -> Cmp, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{+h, +t}:
      Bool.pick(List<&2, A>, le(~A, ~cmp, x, h), Con{x, Con{h, t}}, Con{h, ins(~A, ~cmp, x, t)})

# The multiset of a list, left to right.
def from_list(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      from_list(~A, ~cmp, t, ins(~A, ~cmp, x, acc))

def item(-A: Data, x: Maybe<&2, A>) -> Result<&2, &2, E.Error, A>:
  match x:
    case None{}:
      Fail{E.EmptyHeap{}}
    case Some{v}:
      Done{v}

def pop(-A: Data, xs: List<&2, A>) -> List<&2, A> & E.Obs<A>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyHeap{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def step(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, op: E.Op<A>) -> List<&2, A> & E.Obs<A>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(A, xs)})
    case E.Push{x}:
      (ins(~A, ~cmp, x, xs), E.OUnit{})
    case E.Peek{}:
      (xs, E.OItem{item(A, C.head(A, xs))})
    case E.Pop{}:
      pop(A, xs)
    case E.FromList{ys}:
      (from_list(~A, ~cmp, ys, Nil{}), E.OUnit{})
    case E.ToSortedList{}:
      (xs, E.OList{xs})

def cons_obs(-A: Data, o: E.Obs<A>, r: List<&2, A> & List<&2, E.Obs<A>>) -> List<&2, A> & List<&2, E.Obs<A>>:
  (m, os) = r
  (m, Con{o, os})

def run(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, +xs: List<&2, A>) -> List<&2, A> & List<&2, E.Obs<A>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(A, Pair.snd(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op)), run(~A, ~cmp, rest, Pair.fst(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op))))
