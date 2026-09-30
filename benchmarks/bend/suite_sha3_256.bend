import Base
import ./suite.bend as S
import ../../src/crypto/hash.bend as H

# SHA3-256 (src/crypto/hash.bend) of every message; C: XKCP Keccak-p[1600] with SHA-3 padding.

def run(xs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, H.sha3_256(h) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
