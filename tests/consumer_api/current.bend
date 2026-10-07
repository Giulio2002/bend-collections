import Base
import ./src/crypto/sign.bend as Sign
import ./src/crypto/ed25519/ed25519.bend as E
import ./src/math/natural.bend as Natural

def present(m: Maybe<&2, E.Key>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{k}:
      1n

def smoke(+seed: List<&2, U32>) -> Nat:
  present(Sign.signing_key(seed))

def main() -> Nat:
  Natural.gcd(12n, 18n)
