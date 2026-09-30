import Base
import ./laws_ecdsa.bend as Laws
import ./group/ecds.bend as EC

# ECDSA correctness on the specification (laws_ecdsa.bend):
# `bend proofs/crypto/secp256k1/proof_ecdsa.bend`.

def Laws.Ecdsa.sign_verify(one, h1, hp, hc, hq, hg, hng, sk, h, c, strict, sig, pk, hs, hpk):
  EC.sign_verify(one, h1, hp, hc, hq, hg, hng, sk, h, c, strict, sig, pk, hs, hpk)

def Laws.Ecdsa.sign_recover(one, h1, hp, hc, hq, hg, hng, sk, h, sig, hs):
  EC.sign_recover(one, h1, hp, hc, hq, hg, hng, sk, h, sig, hs)
