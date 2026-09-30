import Base
import ./suite.bend as S
import ../../src/crypto/mac.bend as MAC

# HMAC-SHA256 (src/crypto/mac.bend) of every message under a fixed 32-byte key.

def run(xs: List<&2, List<&2, U32>>, +key: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, key, MAC.sign(key, h) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +key : List<&2, U32> = S.pattern(32n, 7, 1)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, key, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
