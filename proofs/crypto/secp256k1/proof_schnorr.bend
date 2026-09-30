import Base
import ./lite/crypto/secp256k1/group/certpc.bend as PC
import ./laws_schnorr.bend as Laws
import ./pschn.bend as PSC
import ./pkp.bend as PK
import ../../../spec/crypto/secp256k1/schnorr.bend as SS
import ../../../src/crypto/secp256k1.bend as K

# BIP-340 Schnorr signatures of src/crypto/secp256k1.bend (laws.bend
# SchnorrPubkey.correct, SchnorrSign.correct, SchnorrVerify.correct,
# SchnorrKeypairPubkey.correct, SchnorrSignKeypair.correct):
# `bend proofs/crypto/secp256k1/proof_schnorr.bend`.

def Laws.SchnorrPubkey.correct(one, h1, sk):
  PSC.pubkey_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk)

def Laws.SchnorrSign.correct(one, h1, sk, msg, aux):
  PSC.sign_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk, msg, aux)

def Laws.SchnorrVerify.correct(one, h1, pk, msg, sig):
  PSC.verify_v(one, h1, pk, msg, sig)

def Laws.SchnorrKeypairPubkey.correct(one, h1, sk):
  Equal.trans(Maybe<&2, List<&2, U32>>, K.schnorr_keypair_pubkey(K.schnorr_keypair(sk)), K.schnorr_pubkey(sk), SS.pubkey(one, sk), PK.pub_kp_v(sk), PSC.pubkey_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk))

def Laws.SchnorrSignKeypair.correct(one, h1, sk, msg, aux):
  Equal.trans(Maybe<&2, List<&2, U32>>, K.schnorr_sign_keypair(K.schnorr_keypair(sk), msg, aux), K.schnorr_sign(sk, msg, aux), SS.sign(one, sk, msg, aux), PK.sign_kp_v(sk, msg, aux), PSC.sign_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), sk, msg, aux))
