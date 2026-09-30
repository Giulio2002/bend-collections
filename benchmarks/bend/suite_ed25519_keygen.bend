import Base
import ./suite.bend as S
import ../../src/crypto/sign.bend as E

# Ed25519 key generation (src/crypto/sign.bend generate_keypair): every
# 32-byte message is a seed; the output is the public key.
# C: Monocypher 4.0.2 crypto_ed25519_key_pair.

def public(m: Maybe<&2, E.Keypair>) -> List<&2, U32>:
  match m:
    case None{}:
      [256]
    case Some{E.Keypair{sk, pk}}:
      pk

def run(xs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, public(E.generate_keypair(h)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
