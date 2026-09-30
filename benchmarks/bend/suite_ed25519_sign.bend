import Base
import ./suite.bend as S
import ../../src/crypto/sign.bend as E

# Ed25519 signing (src/crypto/sign.bend sign) of every message under a fixed
# seed (pattern(32, 13, 7)). Note: this API takes the 32-byte seed and
# re-derives the public key (one more base-point multiplication) on every
# call, while the C reference, Monocypher 4.0.2 crypto_ed25519_sign, takes the
# 64-byte secret key seed || public key made once before the timed region.

def run(xs: List<&2, List<&2, U32>>, +sk: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, sk, S.unwrap(E.sign(sk, h)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +sk : List<&2, U32> = S.pattern(32n, 13, 7)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, sk, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
