import Base

# Neutral datatypes shared by src/stack.bend and spec/stack.bend.

type Error is Data:
  EmptyStack{}

type Op<-T: Data> is Data:
  Length{}
  Push{value: T}
  Pop{}
  Peek{}
  ToList{}

type Obs<-T: Data> is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, T>}
  OUnit{}
  OList{items: List<&2, T>}
