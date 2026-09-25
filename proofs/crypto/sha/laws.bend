import Base
import ../../../src/crypto/sha/sha256.bend as SHA
import ../../../spec/crypto/sha.bend as FIPS

# These claims mention the actual public API and the complete independent spec.
# There are no arbitrary preprocessing functions, tables, or correctness premises.
law constants_correct:
  {SHA.constants() == FIPS.constants() : List<&2, U32>}

law sha256_correct:
  for +bytes: List<&2, U32>
  {SHA.sha256(bytes) == FIPS.sha256(bytes) : List<&2, U32>}

law digest_bytes_correct:
  for +ws: List<&2, U32>
  {SHA.digest_bytes(ws) == FIPS.digest_octets(ws) : List<&2, U32>}

law sha256_bytes_correct:
  for +bytes: List<&2, U32>
  {SHA.sha256_bytes(bytes) == FIPS.sha256_bytes(bytes) : List<&2, U32>}

law sha256_bytes_length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, SHA.sha256_bytes(bytes)) == 32n : Nat}
