import Base
import ./common.bend as C
import ../types/stack.bend as E

# Independent LIFO sequence model; top is the first element.
def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match xs op:
    case +ys E.Push{x}:
      (Con{x, ys}, E.OUnit{})
    case +ys E.Length{}:
      (ys, E.ONat{C.length(T, ys)})
    case +ys E.ToList{}:
      (ys, E.OList{ys})
    case Nil{} E.Pop{}:
      (Nil{}, E.OItem{Fail{E.EmptyStack{}}})
    case Con{x, tail} E.Pop{}:
      (tail, E.OItem{Done{x}})
    case Nil{} E.Peek{}:
      (Nil{}, E.OItem{Fail{E.EmptyStack{}}})
    case Con{+x, +tail} E.Peek{}:
      (Con{x, tail}, E.OItem{Done{x}})
