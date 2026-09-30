import Base
import ../../../src/crypto/sha3/sha3_256.bend as SHA3
import ../../../spec/crypto/sha3.bend as FIPS

# SHA3-256: the public API against the FIPS 202 specification
# spec/crypto/sha3.bend (sponge on the specification's Keccak-p[1600, 24]).

# The digest of every byte list is the specification's.
law sha3_256_correct:
  for +bytes: List<&2, U32>
  {SHA3.sha3_256(bytes) == FIPS.sha3_256(bytes) : List<&2, U32>}

# Every digest is 32 bytes.
law sha3_256_length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, SHA3.sha3_256(bytes)) == 32n : Nat}
