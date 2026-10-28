import Base
import ./src/crypto/sign.bend as Sign
import ./src/math/natural.bend as Natural

def smoke(+seed: List<&2, U32>) -> Maybe<&2, Sign.Keypair>:
  Sign.generate_keypair(seed)

def main() -> Nat:
  Natural.gcd(12n, 18n)
