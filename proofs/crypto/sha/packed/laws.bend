import Base
import ../../../../src/crypto/sha/packed/sha256.bend as Runtime
import ../../../../src/crypto/sha/packed/buffer.bend as Buffer
import ./legacy_model.bend as SHA
import ../../../../spec/crypto/sha.bend as FIPS
import ../../../../spec/crypto/sha/packed.bend as PackedSpec

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

# A separate packed-format contract; the original list-to-FIPS theorem is unchanged.
law sha256_packed_correct:
  for words: Array<U32>
  for +byte_length: Nat
  {SHA.sha256_packed(words,byte_length) == PackedSpec.sha256(words,byte_length) : Maybe<&2,List<&2,U32>>}

# Actual production array API; historical list laws above concern only its model.
law sha256_array_correct:
  for words: Array<U32>
  for +byte_length: Nat
  {Runtime.sha256(words,byte_length) == Buffer.result(PackedSpec.hash(words,byte_length)) : Maybe<&1,Array<U32>>}
