import Base
import ./laws_schnorr.bend as Laws
import ./pschn.bend as PSC

# BIP-340 Schnorr signatures of src/crypto/secp256k1.bend (laws.bend
# SchnorrPubkey.correct, SchnorrSign.correct, SchnorrVerify.correct):
# `bend proofs/crypto/secp256k1/proof_schnorr.bend`.

def Laws.SchnorrPubkey.correct(one, h1, sk):
  PSC.pubkey_v(one, h1, sk)

def Laws.SchnorrSign.correct(one, h1, sk, msg, aux):
  PSC.sign_v(one, h1, sk, msg, aux)

def Laws.SchnorrVerify.correct(one, h1, pk, msg, sig):
  PSC.verify_v(one, h1, pk, msg, sig)
