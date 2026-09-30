import Base

# Constant-time comparison of byte strings, after Go's crypto/subtle
# (ConstantTimeCompare) and HACL*'s Lib.ByteBuffer.lbytes_eq.
#
# Bytes are U32 values (each < 256 in the byte convention; any U32 works).
# The lengths are public: lists of different lengths are unequal, decided on
# the lengths alone. For equal lengths, every position is read: the XOR of
# the two bytes is ORed into an accumulator, with no early exit and no branch
# on the contents, and the result is whether the accumulator is zero.
#
# Bend has no timing model, so "constant time" is a property of this code's
# shape (one pass, no data-dependent match), not a proved fact. What is proved
# (proofs/crypto/subtle/) is its value: eq(a, b) is True exactly when a == b.

# OR of the XOR of every pair of positions, over the common prefix.
def diff(a: List<&2, U32>, b: List<&2, U32>, acc: U32) -> U32:
  match a b:
    case x <> xs y <> ys:
      diff(xs, ys, U32.or(acc, U32.xor(x, y)))
    case _ _:
      acc

# True exactly when a and b are the same list.
def eq(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, U32, a), List.length(&2, U32, b)),
    U32.is_eq(diff(a, b, 0), 0))
