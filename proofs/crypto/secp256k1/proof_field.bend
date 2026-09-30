import Base
import ./laws_field.bend as Laws
import ./group/certpc.bend as PC

# The primality of p and the cube fact (laws_field.bend):
# `bend proofs/crypto/secp256k1/proof_field.bend`.

def Laws.Field.prime(one, h1):
  PC.prime_p(one, h1)

def Laws.Field.not_cube(one, h1):
  PC.cube_spec(one, h1)
