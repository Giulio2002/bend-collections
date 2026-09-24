import Base

# Neutral datatypes shared by src/containers/bitlist.bend and its spec.

type Error is Data:
  IndexOutOfRange{}
  Full{}
  Empty{}

# One public operation, for arbitrary finite operation traces.
type Op is Data:
  Length{}
  Limit{}
  Get{index: Nat}
  Assign{index: Nat, value: Bool}
  Push{value: Bool}
  Pop{}
  Clear{}
  Count{}
  ToList{}

# The observable answer of one operation.
type Obs is Data:
  ONat{value: Nat}
  OLimit{limit: Maybe<&2, Nat>}
  OBit{result: Result<&2, &2, Error, Bool>}
  OUnit{result: Result<&2, &2, Error, Unit>}
  OBits{bits: List<&2, Bool>}
