import Base

# Neutral datatypes shared by src/deque.bend and spec/deque.bend.

type Error is Data:
  EmptyDeque{}

type Op<-T: Data> is Data:
  Length{}
  PushFront{value: T}
  PushBack{value: T}
  PopFront{}
  PopBack{}
  PeekFront{}
  PeekBack{}
  ToList{}

type Obs<-T: Data> is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, T>}
  OUnit{}
  OList{items: List<&2, T>}
