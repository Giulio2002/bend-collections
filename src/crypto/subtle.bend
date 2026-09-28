import Base

# Constant-time helpers (placeholder until src/crypto/subtle.bend of the
# crypto-hash branch lands; same API).

# OR of the XOR of every pair of bytes: zero exactly when the lists agree
# on their common prefix. No early exit: every pair is visited.
def diff(a: List<&2, U32>, b: List<&2, U32>, acc: U32) -> U32:
  match a b:
    case Nil{} _:
      acc
    case x <> xs Nil{}:
      acc
    case x <> xs y <> ys:
      diff(xs, ys, U32.or(acc, U32.xor(x, y)))

def eq_if(a: List<&2, U32>, b: List<&2, U32>, same_length: Bool) -> Bool:
  match same_length:
    case True{}:
      U32.is_eq(diff(a, b, 0), 0)
    case False{}:
      False{}

# Constant-time equality of byte lists; the lengths are public.
def eq(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  eq_if(a, b, Nat.is_eq(List.length(&2, U32, a), List.length(&2, U32, b)))
