import Base
import ./curve25519/field.bend as FS
import ./curve25519/x25519.bend as S
import ../../src/crypto/kex.bend as K

# The contract of src/crypto/kex.bend (X25519 key exchange, RFC 7748).
# `one` is the symbolic 1 of spec/crypto/curve25519/field.bend.
#
#   clause          statement
#   Kex.public      generate_keypair(seed) has the public key X25519(seed, 9)
#   Kex.shared      shared_secret(sk, pk) is X25519(sk, pk), or None when it
#                   is all zero (RFC 7748 section 6.1)
#   Kex.reject      malformed input gives None

def base() -> List<&2, U32>:
  [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def unless_zero(ss: List<&2, U32>, z: Bool) -> Maybe<&2, List<&2, U32>>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{ss}

def Kex.public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {K.generate_keypair(seed) == Some{K.Keypair{seed, S.x25519(one, seed, base())}} : Maybe<&2, K.Keypair>}

def Kex.shared(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +pk: List<&2, U32>, +hs: {FS.tight(sk) == True{} : Bool}, +hp: {FS.tight(pk) == True{} : Bool}) -> Type:
  {K.shared_secret(sk, pk) == unless_zero(S.x25519(one, sk, pk), Nat.is_eq(FS.value(S.x25519(one, sk, pk)), 0n)) : Maybe<&2, List<&2, U32>>}

def Kex.reject(+sk: List<&2, U32>, +pk: List<&2, U32>, +h: {Bool.and(FS.tight(sk), FS.tight(pk)) == False{} : Bool}) -> Type:
  {K.shared_secret(sk, pk) == None{} : Maybe<&2, List<&2, U32>>}
