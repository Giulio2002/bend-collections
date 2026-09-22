import Base

# Neutral datatypes shared by src/dynamic_array.bend and spec/dynamic_array.bend.

type Error is Data:
  IndexOutOfRange{}
  EmptyArray{}
  CapacityExceeded{}

# One public operation, for arbitrary finite operation traces.
type Op<-T: Data> is Data:
  Length{}
  Capacity{}
  Get{index: Nat}
  Set{index: Nat, value: T}
  Push{value: T}
  Pop{}
  Reserve{wanted: Nat}
  Clear{}
  ToList{}

# The observable answer of one operation.
type Obs<-T: Data> is Data:
  ONat{value: Nat}
  OItem{result: Result<&2, &2, Error, T>}
  OUnit{result: Result<&2, &2, Error, Unit>}
  OList{items: List<&2, T>}

# A rejected owning write returns its input value to the caller.
type Rejected<-T: Type> is Type:
  Rejected{error: Error, value: T}
