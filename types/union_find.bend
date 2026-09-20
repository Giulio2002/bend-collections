import Base

# Neutral datatypes shared by src/union_find.bend and spec/union_find.bend.

type Error is Data:
  OutOfRange{}

type Op is Data:
  Find{x: Nat}
  Union{a: Nat, b: Nat}
  Connected{a: Nat, b: Nat}
  ComponentSize{x: Nat}
  ComponentCount{}

type Obs is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, Nat>}
  OBool{result: Result<&2, &2, Error, Bool>}
