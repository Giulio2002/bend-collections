import Base
import ./group/certpc.bend as PC
import ../../../src/crypto/secp256k1.bend as K
import ../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ./laws.bend as Laws
import ./ppub.bend as PP
import ./peth.bend as PE

# Gate for src/crypto/secp256k1.bend, keys and addresses:
# `bend proofs/crypto/secp256k1/proof.bend`. The other clauses of laws.bend
# are proved in the roots proof_sign.bend, proof_verify.bend,
# proof_recover.bend and proof_schnorr.bend (each checks alone; together
# they check every clause).

def Laws.PublicKey.correct(one, h1, sk, c):
  PP.public_key_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk, c)

def gk(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>) -> {K.generate_keypair(seed) == K.keypair_of(seed, ES.public_key(one, seed, True{})) : Maybe<&2, K.Keypair>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, K.Keypair>, m => K.keypair_of(seed, m), K.public_key(seed, True{}), ES.public_key(one, seed, True{}), PP.public_key_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), seed, True{}))

def Laws.GenerateKeypair.correct(one, h1, seed):
  gk(one, h1, seed)

def Laws.EthAddress.correct(pk):
  PE.eth_address_v(pk)
