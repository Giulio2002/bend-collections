import Base

# Neutral datatypes shared by src/segment_tree.bend and spec/segment_tree.bend.

type Error is Data:
  IndexOutOfRange{}
  InvalidRange{}

type Op is Data:
  Length{}
  Get{index: Nat}
  Set{index: Nat, value: U32}
  RangeQuery{start: Nat, end: Nat}
  RangeAdd{start: Nat, end: Nat, delta: U32}

type Obs is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, U32>}
  OUnit{result: Result<&2, &2, Error, Unit>}
