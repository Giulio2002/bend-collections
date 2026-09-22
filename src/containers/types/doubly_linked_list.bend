import Base

# Neutral datatypes shared by src/doubly_linked_list.bend and
# spec/doubly_linked_list.bend.

type Error is Data:
  ForeignHandle{}
  StaleHandle{}

# A handle identifies the list, physical slot and its incarnation.
# Generation zero is the first incarnation. Exhausted slots are retired;
# generation never wraps and old handles never become valid again.
type Handle is Data:
  H{list: U32, id: U32, generation: U32}

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
