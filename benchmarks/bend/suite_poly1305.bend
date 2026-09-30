import Base
import ./suite.bend as S
import ../../src/crypto/poly1305/poly1305.bend as P

# The Poly1305 tag (RFC 8439, src/crypto/poly1305/poly1305.bend) of every
# message under a fixed 32-byte one-time key.

def run(xs: List<&2, List<&2, U32>>, +key: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, key, S.unwrap(P.poly1305(key, h)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +key : List<&2, U32> = S.pattern(32n, 7, 1)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, key, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
