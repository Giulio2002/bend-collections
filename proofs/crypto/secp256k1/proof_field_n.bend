import Base
import ./laws_field_n.bend as Laws
import ./group/certn.bend as CN

# The group order is prime (laws_field_n.bend):
# `bend proofs/crypto/secp256k1/proof_field_n.bend`.

def Laws.Field.order_prime(one, h1):
  CN.prime_n(one, h1)
