import Base

# Neutral datatypes shared by src/binary_heap.bend and spec/binary_heap.bend.

type Error is Data:
  EmptyHeap{}

type Op<-A: Data> is Data:
  Length{}
  Push{value: A}
  Peek{}
  Pop{}
  FromList{items: List<&2, A>}
  ToSortedList{}

type Obs<-A: Data> is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, A>}
  OUnit{}
  OList{items: List<&2, A>}
