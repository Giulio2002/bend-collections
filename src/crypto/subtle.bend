import Base

# Constant-time comparison of byte strings, after Go's crypto/subtle
# (ConstantTimeCompare) and HACL*'s Lib.ByteBuffer.lbytes_eq.
#
# Bytes are U32 values (each < 256 in the byte convention; any U32 works, so
# the same function compares lists of 32-bit words, e.g. four bytes packed
# per word: a quarter of the steps for the same data). The lengths are
# public: lists of different lengths are unequal. One pass walks both lists
# together: the XOR of each pair is ORed into an accumulator, with no early
# exit and no branch on the contents; the result is whether both lists end
# together with the accumulator zero. (The pass stops where the shorter list
# ends: only the lengths, which are public, steer it.)
#
# Bend has no timing model, so "constant time" is a property of this code's
# shape (one pass, no data-dependent match), not a proved fact. What is proved
# (proofs/crypto/subtle/) is its value: eq(a, b) is True exactly when a == b.

# The pass: True when a and b end together and acc | (a[i] ^ b[i]) is zero.
def go(a: List<&2, U32>, b: List<&2, U32>, acc: U32) -> Bool:
  match a b:
    case x <> xs y <> ys:
      go(xs, ys, U32.or(acc, U32.xor(x, y)))
    case Nil{} Nil{}:
      U32.is_eq(acc, 0)
    case _ _:
      False{}

# The same pass four pairs per step (one match and one accumulator update
# per four pairs), then go for the last 0..3 pairs.
def go4(a: List<&2, U32>, b: List<&2, U32>, acc: U32) -> Bool:
  match a b:
    case x0 <> x1 <> x2 <> x3 <> at y0 <> y1 <> y2 <> y3 <> bt:
      go4(at, bt, U32.or(acc, U32.or(U32.or(U32.xor(x0, y0), U32.xor(x1, y1)), U32.or(U32.xor(x2, y2), U32.xor(x3, y3)))))
    case _ _:
      go(a, b, acc)

# True exactly when a and b are the same list.
def eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  go4(a, b, 0)
