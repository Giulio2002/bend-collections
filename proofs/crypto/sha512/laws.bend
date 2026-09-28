import Base
import ../../../src/crypto/sha512/types.bend as T
import ../../../src/crypto/sha512/sha512.bend as SHA
import ../../../spec/crypto/sha512.bend as FIPS

# SHA-512: the public API against the complete, independent FIPS 180-4
# specification spec/crypto/sha512.bend. No test vector, table or premise.

# The digest of every byte list is the specification's.
law sha512_correct:
  for +bytes: List<&2, U32>
  {SHA.sha512(bytes) == FIPS.sha512_bytes(bytes) : List<&2, U32>}

# Every digest is 64 bytes.
law sha512_length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, SHA.sha512(bytes)) == 64n : Nat}
