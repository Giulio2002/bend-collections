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
# (proof_schnorr.bend). This file: proof.bend.

# the SEC 1 public key (33 bytes compressed, 65 uncompressed) of [d] G
law PublicKey.correct:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +sk: List<&2, U32>
  for c: Bool
  {K.public_key(sk, c) == ES.public_key(one, sk, c) : Maybe<&2, List<&2, U32>>}

# a key pair from a 32-byte seed: the seed and its compressed public key
law GenerateKeypair.correct:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +seed: List<&2, U32>
  {K.generate_keypair(seed) == K.keypair_of(seed, ES.public_key(one, seed, True{})) : Maybe<&2, K.Keypair>}

# the Ethereum address of an uncompressed public key
law EthAddress.correct:
  for +pk: List<&2, U32>
  {K.eth_address(pk) == ES.eth_address(pk) : Maybe<&2, List<&2, U32>>}
