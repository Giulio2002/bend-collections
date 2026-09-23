import Base
import ../../lib/spec_common.bend as C
import ../../../src/containers/types/queue.bend as E

# Independent model: a FIFO queue is the sequence of its elements, oldest
# first. Enqueue appends at the end; dequeue removes the first element.

def item(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.EmptyQueue{}}
    case Some{v}:
      Done{v}

def dequeue(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyQueue{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(T, xs)})
    case E.Enqueue{x}:
      (C.snoc(T, xs, x), E.OUnit{})
    case E.Dequeue{}:
      dequeue(T, xs)
    case E.Peek{}:
      (xs, E.OItem{item(T, C.head(T, xs))})
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
