import Base
import ../support/text.bend as X
import ../crypto/bytes.bend as B

# Helpers shared by the backend-differential drivers (tools/backend_diff.py).
# Test-only; never imported by src/ or proofs/.

def bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def opt(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "none"
    case Some{x}:
      B.hex(x)

# field i of a token, as bytes (lower-case hex; the empty field is no bytes)
def hexf(p: List<&2, String>, i: Nat) -> List<&2, U32>:
  B.unhex(X.field(p, i))
