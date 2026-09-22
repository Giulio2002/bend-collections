import Base

# Neutral datatypes shared by src/queue.bend and spec/queue.bend.

type Error is Data:
  EmptyQueue{}

type Op<-T: Data> is Data:
  Length{}
  Enqueue{value: T}
  Dequeue{}
  Peek{}
  ToList{}

type Obs<-T: Data> is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, T>}
  OUnit{}
  OList{items: List<&2, T>}
