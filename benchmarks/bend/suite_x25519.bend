import Base
import ./suite.bend as S
import ../../src/crypto/kex.bend as K
import ../../src/crypto/curve25519/x25519.bend as X

# X25519 shared secret (src/crypto/kex.bend shared_secret): every 32-byte
# message is a secret key, the peer public key is fixed (X25519 of
# pattern(32, 9, 5) with the base point, computed before the timed region).
# C: Monocypher 4.0.2 crypto_x25519.

def run(xs: List<&2, List<&2, U32>>, +pk: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, pk, S.unwrap(K.shared_secret(h, pk)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +pk : List<&2, U32> = S.unwrap(X.x25519(S.pattern(32n, 9, 5), X.base()))
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, pk, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
