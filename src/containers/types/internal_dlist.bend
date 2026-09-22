import Base

# Neutral datatypes shared by src/doubly_linked_list.bend and
# spec/doubly_linked_list.bend.

type Error is Data:
  ForeignHandle{}
  StaleHandle{}

# Opaque element handle: the owning list's tag and the element's id. Both are
# U32: an id is a slot index of the implementation's arena (never reused) and
# a tag identifies the owning list, so both comparisons are one machine
# operation.
type Handle is Data:
  H{list: U32, id: U32}

type Item<-T: Data> is Data:
  Item{id: U32, val: T}

type Op<-T: Data> is Data:
  Length{}
  PushFront{x: T}
  PushBack{x: T}
  InsertBefore{h: Handle, x: T}
  InsertAfter{h: Handle, x: T}
  Remove{h: Handle}
  Get{h: Handle}
  Set{h: Handle, x: T}
  Next{h: Handle}
  Prev{h: Handle}
  ToList{}

type Obs<-T: Data> is Data:
  ONat{n: Nat}
  OHandle{h: Handle}
  OInsert{result: Result<&2, &2, Error, Handle>}
  OVal{result: Result<&2, &2, Error, T>}
  OUnit{result: Result<&2, &2, Error, Unit>}
  ONbr{result: Result<&2, &2, Error, Maybe<&2, Handle>>}
  OList{xs: List<&2, T>}
