import Base

# Neutral datatypes shared by src/fenwick_tree.bend and spec/fenwick_tree.bend.

type Error is Data:
  IndexOutOfRange{}
  InvalidRange{}

type Op is Data:
  Length{}
  Add{index: Nat, delta: U32}
  PrefixSum{end: Nat}
  RangeSum{start: Nat, end: Nat}

type Obs is Data:
  ONat{value: Nat}
  OSum{result: Result<&2, &2, Error, U32>}
  OUnit{result: Result<&2, &2, Error, Unit>}
