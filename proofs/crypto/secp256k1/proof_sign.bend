import Base
import ./group/certpc.bend as PC
import ../../../src/crypto/secp256k1.bend as K
import ../../../src/crypto/secp256k1/ecdsa.bend as E
import ../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ./laws_sign.bend as Laws
import ./psign.bend as PS

# ECDSA signing of src/crypto/secp256k1.bend (laws.bend Sign.correct):
# `bend proofs/crypto/secp256k1/proof_sign.bend`.

def compact_v(m: Maybe<&2, E.Signature>) -> {K.compact(m) == PS.msig(m) : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{sig}:
      match sig:
        case E.Signature{r, s, v}:
          {==}

def sign_c(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +h: List<&2, U32>) -> {K.sign_compact(sk, h) == ES.sign(one, sk, h) : Maybe<&2, List<&2, U32>>}:
  Equal.trans(Maybe<&2, List<&2, U32>>, K.compact(E.sign(sk, h)), PS.msig(E.sign(sk, h)), ES.sign(one, sk, h), compact_v(E.sign(sk, h)), PS.sign_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk, h))

def Laws.Sign.correct(one, h1, sk, h):
  sign_c(one, h1, sk, h)
