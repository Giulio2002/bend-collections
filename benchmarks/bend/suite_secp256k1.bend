import Base
import ./suite.bend as S
import ../../src/crypto/secp256k1.bend as K
import ../../src/crypto/secp256k1/schnorr.bend as Sch

# secp256k1 (src/crypto/secp256k1.bend) on 32-byte messages (message hashes)
# under the fixed secret key pattern(32, 17, 3). BENCH_PARAM: 0 ECDSA
# sign_compact (RFC 6979, low s; r || s || recovery id), 1 ECDSA verify
# (33-byte compressed key, r || s), 2 recover (the 65-byte public key),
# 3 BIP-340 schnorr_sign_keypair (aux = pattern(32, 19, 1); the key pair made
# before the timed region, as libsecp256k1's secp256k1_keypair), 4 BIP-340
# schnorr_verify.
# Signatures for 1, 2 and 4 are made before the timed region.
# C: libsecp256k1 v0.6.0.

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      Nil{}
    case _ Nil{}:
      Nil{}
    case 1n+p h <> t:
      h <> take(p, t)

# the untimed input of op for message h
def prep(+op: Nat, +sk: List<&2, U32>, +aux: List<&2, U32>, +h: List<&2, U32>) -> List<&2, U32>:
  match op:
    case 0n:
      Nil{}
    case 1n+a:
      match a:
        case 0n:
          take(64n, S.unwrap(K.sign_compact(sk, h)))
        case 1n+b:
          match b:
            case 0n:
              S.unwrap(K.sign_compact(sk, h))
            case 1n+c:
              match c:
                case 0n:
                  Nil{}
                case 1n+d:
                  S.unwrap(K.schnorr_sign(sk, h, aux))

def preps(xs: List<&2, List<&2, U32>>, +op: Nat, +sk: List<&2, U32>, +aux: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      prep(op, sk, aux, h) <> preps(t, op, sk, aux)

def apply(+op: Nat, +sk: List<&2, U32>, +kp: Maybe<&2, Sch.Keypair>, +pk: List<&2, U32>, +xpk: List<&2, U32>, +aux: List<&2, U32>, h: List<&2, U32>, g: List<&2, U32>) -> List<&2, U32>:
  match op:
    case 0n:
      S.unwrap(K.sign_compact(sk, h))
    case 1n+a:
      match a:
        case 0n:
          S.bit(K.verify(pk, h, g))
        case 1n+b:
          match b:
            case 0n:
              S.unwrap(K.recover(h, g))
            case 1n+c:
              match c:
                case 0n:
                  S.unwrap(K.schnorr_sign_keypair(kp, h, aux))
                case 1n+d:
                  S.bit(K.schnorr_verify(xpk, h, g))

def run(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>, +op: Nat, +sk: List<&2, U32>, +kp: Maybe<&2, Sch.Keypair>, +pk: List<&2, U32>, +xpk: List<&2, U32>, +aux: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs ys:
    case h <> t g <> u:
      run(t, u, op, sk, kp, pk, xpk, aux, apply(op, sk, kp, pk, xpk, aux, h, g) <> acc)
    case _ _:
      acc

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    msgs : List<&2, List<&2, U32>> <- S.messages()
    +op : Nat <- S.env_nat("BENCH_PARAM")
    +sk : List<&2, U32> = S.pattern(32n, 17, 3)
    +aux : List<&2, U32> = S.pattern(32n, 19, 1)
    +pk : List<&2, U32> = S.unwrap(K.public_key(sk, True{}))
    +xpk : List<&2, U32> = S.unwrap(K.schnorr_pubkey(sk))
    +kp : Maybe<&2, Sch.Keypair> = K.schnorr_keypair(sk)
    extra : List<&2, List<&2, U32>> = preps(inputs, op, sk, aux)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(msgs, extra, op, sk, kp, pk, xpk, aux, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
