import Base
import ./lite/crypto/secp256k1/group/certpc.bend as PC
import ./laws_verify.bend as Laws
import ./pver.bend as PV

# ECDSA verification of src/crypto/secp256k1.bend (laws.bend Verify.correct,
# VerifyStrict.correct): `bend proofs/crypto/secp256k1/proof_verify.bend`.

def Laws.Verify.correct(one, h1, pk, h, sig):
  PV.verify_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), pk, h, sig, False{})

def Laws.VerifyStrict.correct(one, h1, pk, h, sig):
  PV.verify_v(one, h1, PC.prime_p(one, h1), PC.cube_spec(one, h1), pk, h, sig, True{})
