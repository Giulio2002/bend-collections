import Base
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ../../math/number/nt_prime.bend as PM

# ECDSA correctness on the specification
# (spec/crypto/secp256k1/ecdsa.bend: SEC 1 signing with the RFC 6979 nonce
# and low-S output, verification, public key recovery), for every input;
# `one` is the number 1 kept symbolic (h1), as in the other secp256k1
# clauses.
#
# Each clause takes these facts about the curve as hypotheses; each is a
# closed statement proved in a root of its own (closed computations that
# fill a root each):
#   hp:  p = FS.prime(one) is prime                  (group/certa.bend)
#   hc:  (-7)^((p - 1) / 3) != 1 in GF(p)            (group/certd.bend)
#   hq:  n = FS.order(one) is prime                  (group/certn.bend)
#   hg:  G is a point of the group                   (group/ptv.bend)
#   hng: [n] G is the point at infinity              (group/pte.bend)
# Proved by `bend proofs/crypto/secp256k1/proof_ecdsa.bend`.

# every signature that sign returns verifies under the signer's public key
# (compressed or not), also strictly (its s is low); sign returns
# r || s || v and verify takes r || s
law Ecdsa.sign_verify:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +sk: List<&2, U32>
  for +h: List<&2, U32>
  for +c: Bool
  for +strict: Bool
  for +sig: List<&2, U32>
  for +pk: List<&2, U32>
  for +hs: {ES.sign(one, sk, h) == Some{sig} : Maybe<&2, List<&2, U32>>}
  for +hpk: {ES.public_key(one, sk, c) == Some{pk} : Maybe<&2, List<&2, U32>>}
  {ES.verify(one, pk, h, CS.first(64n, sig), strict) == True{} : Bool}

# recover on a signature that sign returned gives the signer's uncompressed
# public key
law Ecdsa.sign_recover:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +sk: List<&2, U32>
  for +h: List<&2, U32>
  for +sig: List<&2, U32>
  for +hs: {ES.sign(one, sk, h) == Some{sig} : Maybe<&2, List<&2, U32>>}
  {ES.recover(one, h, sig) == ES.public_key(one, sk, False{}) : Maybe<&2, List<&2, U32>>}
