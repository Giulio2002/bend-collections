import Base
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/subtle.bend as Spec

# The clauses of spec/crypto/subtle.bend. Proved in proof.bend.

# eq returns the reference list equality.
law Eq.value:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Subtle.eq(a, b) == Spec.equal(a, b) : Bool}

# eq is True only for equal lists.
law Eq.sound:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {Subtle.eq(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

# eq is True on equal lists.
law Eq.refl:
  for +a: List<&2, U32>
  {Subtle.eq(a, a) == True{} : Bool}
