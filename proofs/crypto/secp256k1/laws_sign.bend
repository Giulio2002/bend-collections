import Base
import ../../../src/crypto/secp256k1.bend as K
import ../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ../../../spec/crypto/secp256k1/schnorr.bend as SS

# The clauses of src/crypto/secp256k1.bend: every function is its
# specification (spec/crypto/secp256k1/, over the natural numbers, from
# SEC 1 v2, SEC 2, RFC 6979, BIP-340 and the Ethereum yellow paper) for
# every input (any byte lists, any Bool). The specification takes `one`,
# the number 1 kept symbolic (h1: one == 1), so that its 256-bit constants
# p, n and G are never expanded by the checker; every clause holds for the
# one `one` there is.
#
# The clauses are in five files, each proved by its own root (so that
# each root checks alone): laws.bend (keys and addresses, proof.bend),
# laws_sign.bend (proof_sign.bend), laws_verify.bend (proof_verify.bend),
# laws_recover.bend (proof_recover.bend) and laws_schnorr.bend
# (proof_schnorr.bend). This file: proof_sign.bend.

# ECDSA signing: RFC 6979 nonce, low s, recovery id; r || s || v
law Sign.correct:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +sk: List<&2, U32>
  for +h: List<&2, U32>
  {K.sign_compact(sk, h) == ES.sign(one, sk, h) : Maybe<&2, List<&2, U32>>}
