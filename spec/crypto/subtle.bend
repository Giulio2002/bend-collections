import Base

# Specification of src/crypto/subtle.bend: list equality, decided position by
# position (the reference; it may stop at the first difference, the
# implementation may not). Clauses in proofs/crypto/subtle/laws.bend:
#
#   Eq.value  eq(a, b) == equal(a, b)            (the Bool it returns)
#   Eq.sound  eq(a, b) == True  implies  a == b  (as lists)
#   Eq.refl   eq(a, a) == True
#
# Together: eq(a, b) is True exactly when a == b.

def equal(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(U32.is_eq(x, y), equal(xs, ys))
    case _ _:
      False{}
