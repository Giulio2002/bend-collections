import Base
import ../lib/common.bend as C
import ../../src/math/pow2.bend as P

# Specification of src/math/pow2.bend: the tail-recursive power of two is
# the structural 2^d of spec/lib/common.bend.
#
#   function   clauses        proved in
#   pow2t      Pow2t.value    proofs/math/pow2/pow2.bend (same)

def Pow2t.value(+d: Nat) -> Type:
  {P.pow2t(d) == C.pow2(d) : Nat}
