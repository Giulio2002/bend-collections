import Base
import ./curve25519/field.bend as FS
import ./ed25519.bend as SE
import ../../src/crypto/sign.bend as SG
import ../../src/crypto/ed25519/ed25519.bend as E

# The contract of src/crypto/sign.bend (Ed25519 signatures, RFC 8032).
# `one` is the symbolic 1 of spec/crypto/curve25519/field.bend.
#
#   clause          statement
#   Sign.keypair    generate_keypair(seed) is the seed with the public key
#                   public_key(seed) of spec/crypto/ed25519.bend
#   Sign.sign       sign(sk, msg) is the RFC 8032 signature sign(sk, msg)
#   Sign.verify     verify(pk, msg, sig) is the RFC 8032 verdict
#   Sign.reject     a malformed seed, key or signature gives None / False
#   Sign.key_public signing_key(seed) is a key whose key_public is
#                   public_key(seed)
#   Sign.key_sign   signing_key(seed) is a key under which sign_with_key(k,
#                   msg) is the RFC 8032 signature sign(seed, msg)
#   Sign.reject_signing_key  a malformed seed gives no signing key

# the public key and a signature of an optional expanded key
def key_pub(m: Maybe<&2, E.Key>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{SG.key_public(k)}

def key_sig(m: Maybe<&2, E.Key>, +msg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{SG.sign_with_key(k, msg)}

def Sign.keypair(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {SG.generate_keypair(seed) == Some{SG.Keypair{seed, SE.public_key(one, seed)}} : Maybe<&2, SG.Keypair>}

def Sign.sign(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(sk) == True{} : Bool}) -> Type:
  {SG.sign(sk, msg) == Some{SE.sign(one, sk, msg)} : Maybe<&2, List<&2, U32>>}

def Sign.verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> Type:
  {SG.verify(pk, msg, sig) == SE.verify(one, pk, msg, sig) : Bool}

def Sign.reject_seed(+seed: List<&2, U32>, +h: {FS.tight(seed) == False{} : Bool}) -> Type:
  {SG.generate_keypair(seed) == None{} : Maybe<&2, SG.Keypair>}

def Sign.reject_key(+sk: List<&2, U32>, +msg: List<&2, U32>, +h: {FS.tight(sk) == False{} : Bool}) -> Type:
  {SG.sign(sk, msg) == None{} : Maybe<&2, List<&2, U32>>}

def Sign.reject(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +h: {Bool.and(FS.tight(pk), FS.bytes_ok(64n, sig)) == False{} : Bool}) -> Type:
  {SG.verify(pk, msg, sig) == False{} : Bool}

def Sign.key_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {key_pub(SG.signing_key(seed)) == Some{SE.public_key(one, seed)} : Maybe<&2, List<&2, U32>>}

def Sign.key_sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {key_sig(SG.signing_key(seed), msg) == Some{SE.sign(one, seed, msg)} : Maybe<&2, List<&2, U32>>}

def Sign.reject_signing_key(+seed: List<&2, U32>, +h: {FS.tight(seed) == False{} : Bool}) -> Type:
  {SG.signing_key(seed) == None{} : Maybe<&2, E.Key>}
