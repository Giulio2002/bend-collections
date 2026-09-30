import Base
import ./suite.bend as S
import ../../src/crypto/hash.bend as H

# SHA-512 (src/crypto/hash.bend) of every message; C: Monocypher crypto_sha512.

def run(xs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, H.sha512(h) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
