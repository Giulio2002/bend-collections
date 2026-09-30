import Base
import ./suite.bend as S
import ../../src/crypto/sign.bend as E
import ../../src/crypto/ed25519/ed25519.bend as ED
# Ed25519 signing (src/crypto/sign.bend sign_with_key) of every message under
# the expanded key of a fixed seed (pattern(32, 13, 7)), made before the
# timed region (src/crypto/sign.bend signing_key: curve constants, base point,
# secret scalar, prefix, public key), as the C reference, Monocypher 4.0.2
# crypto_ed25519_sign, takes the 64-byte secret key seed || public key made
# once before the timed region.

def run(xs: List<&2, List<&2, U32>>, +k: ED.Key, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, k, E.sign_with_key(k, h) <> acc)

def key(m: Maybe<&2, ED.Key>) -> ED.Key:
  match m:
    case None{}:
      ED.expand(Nil{})
    case Some{k}:
      k

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +k : ED.Key = key(E.signing_key(S.pattern(32n, 13, 7)))
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, k, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
