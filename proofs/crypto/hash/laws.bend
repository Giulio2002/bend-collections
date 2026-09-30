import Base
import ../../../src/crypto/hash.bend as Hash
import ../../../spec/crypto/sha.bend as FIPS180
import ../../../spec/crypto/sha512.bend as FIPS180_512
import ../../../spec/crypto/sha3.bend as FIPS202

# The clauses of src/crypto/hash.bend. Proved in proof.bend for every input.

# Each one-shot function is its standard's executable specification.
law Sha256.value:
  for +bytes: List<&2, U32>
  {Hash.sha256(bytes) == FIPS180.sha256_bytes(bytes) : List<&2, U32>}

law Sha512.value:
  for +bytes: List<&2, U32>
  {Hash.sha512(bytes) == FIPS180_512.sha512_bytes(bytes) : List<&2, U32>}

law Sha3_256.value:
  for +bytes: List<&2, U32>
  {Hash.sha3_256(bytes) == FIPS202.sha3_256(bytes) : List<&2, U32>}

# Digest sizes: 32, 64 and 32 bytes.
law Sha256.length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, Hash.sha256(bytes)) == 32n : Nat}

law Sha512.length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, Hash.sha512(bytes)) == 64n : Nat}

law Sha3_256.length:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, Hash.sha3_256(bytes)) == 32n : Nat}

# Incremental hashing equals one-shot hashing for every split of the input:
# the chunks, in order, digest to the hash of their concatenation.
law Incremental.sha256:
  for +chunks: List<&2, List<&2, U32>>
  {Hash.digest(Hash.update_all(Hash.new_sha256(), chunks)) == Hash.sha256(List.concat(&2, U32, chunks)) : List<&2, U32>}

law Incremental.sha512:
  for +chunks: List<&2, List<&2, U32>>
  {Hash.digest(Hash.update_all(Hash.new_sha512(), chunks)) == Hash.sha512(List.concat(&2, U32, chunks)) : List<&2, U32>}

law Incremental.sha3_256:
  for +chunks: List<&2, List<&2, U32>>
  {Hash.digest(Hash.update_all(Hash.new_sha3_256(), chunks)) == Hash.sha3_256(List.concat(&2, U32, chunks)) : List<&2, U32>}

# The two-chunk case, spelled with update.
law Split.sha256:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Hash.digest(Hash.update(Hash.update(Hash.new_sha256(), a), b)) == Hash.sha256(List.append(&2, U32, a, b)) : List<&2, U32>}

law Split.sha512:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Hash.digest(Hash.update(Hash.update(Hash.new_sha512(), a), b)) == Hash.sha512(List.append(&2, U32, a, b)) : List<&2, U32>}

law Split.sha3_256:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Hash.digest(Hash.update(Hash.update(Hash.new_sha3_256(), a), b)) == Hash.sha3_256(List.append(&2, U32, a, b)) : List<&2, U32>}
