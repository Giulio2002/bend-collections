import Base
import ./laws_recover.bend as Laws
import ./prec.bend as PR
import ./pecr.bend as PEC

# Public key recovery and Ethereum's ECRECOVER precompile of
# src/crypto/secp256k1.bend (laws.bend Recover.correct, Ecrecover.correct):
# `bend proofs/crypto/secp256k1/proof_recover.bend`.

def Laws.Recover.correct(one, h1, h, sig):
  PR.recover_v(one, h1, h, sig)

def Laws.Ecrecover.correct(one, h1, input):
  PEC.ecrecover_v(one, h1, input)
