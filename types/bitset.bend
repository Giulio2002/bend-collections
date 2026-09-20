import Base

# Neutral datatypes shared by src/bitset.bend and spec/bitset.bend.

type Error is Data:
  IndexOutOfRange{}
  LengthMismatch{}

# Binary operations carry the operand as its logical bit sequence (bit 0
# first); the runner builds the operand bitset with the public from_bools.
type Op is Data:
  Length{}
  Get{index: Nat}
  Set{index: Nat}
  Clear{index: Nat}
  Count{}
  Union{other: List<&2, Bool>}
  Intersection{other: List<&2, Bool>}
  Difference{other: List<&2, Bool>}
  Xor{other: List<&2, Bool>}
  ToList{}

type Obs is Data:
  ONat{value: Nat}
  OBit{result: Result<&2, &2, Error, Bool>}
  OUnit{result: Result<&2, &2, Error, Unit>}
  OList{members: List<&2, Nat>}
