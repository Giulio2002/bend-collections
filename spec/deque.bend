import Base
import ./common.bend as C
import ../types/deque.bend as E

# Independent model: a deque is the finite sequence of its elements, front
# first. Nothing here refers to the two-list representation.

def item(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.EmptyDeque{}}
    case Some{v}:
      Done{v}

def pop_front(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyDeque{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def pop_back(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyDeque{}}})
    case Con{+h, +t}:
      (C.init(T, Con{h, t}), E.OItem{item(T, C.last(T, Con{h, t}))})

def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(T, xs)})
    case E.PushFront{x}:
      (Con{x, xs}, E.OUnit{})
    case E.PushBack{x}:
      (C.snoc(T, xs, x), E.OUnit{})
    case E.PopFront{}:
      pop_front(T, xs)
    case E.PopBack{}:
      pop_back(T, xs)
    case E.PeekFront{}:
      (xs, E.OItem{item(T, C.head(T, xs))})
    case E.PeekBack{}:
      (xs, E.OItem{item(T, C.last(T, xs))})
    case E.ToList{}:
      (xs, E.OList{xs})

def cons_obs(-T: Data, o: E.Obs<T>, r: List<&2, T> & List<&2, E.Obs<T>>) -> List<&2, T> & List<&2, E.Obs<T>>:
  (m, os) = r
  (m, Con{o, os})

def run(-T: Data, ops: List<&2, E.Op<T>>, +xs: List<&2, T>) -> List<&2, T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(T, Pair.snd(List<&2, T>, E.Obs<T>, step(T, xs, op)), run(T, rest, Pair.fst(List<&2, T>, E.Obs<T>, step(T, xs, op))))
