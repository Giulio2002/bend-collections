import Base
import ./suite.bend as S
import ../../src/crypto/chacha/chacha20.bend as CH

# ChaCha20 (RFC 8439, src/crypto/chacha/chacha20.bend) encryption of every
# message: fixed 32-byte key and 12-byte nonce, initial block counter 1.

def run(xs: List<&2, List<&2, U32>>, +key: List<&2, U32>, +nonce: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, key, nonce, S.unwrap(CH.chacha20(key, 1, nonce, h)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +key : List<&2, U32> = S.pattern(32n, 7, 1)
    +nonce : List<&2, U32> = S.pattern(12n, 3, 5)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, key, nonce, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
