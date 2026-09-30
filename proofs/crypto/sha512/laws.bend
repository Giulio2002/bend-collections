import Base
import ../../../src/crypto/sha512/types.bend as T
import ../../../src/crypto/sha512/sha512.bend as SHA
import ../../../spec/crypto/sha512.bend as FIPS
import ../../../spec/lib/common.bend as C
import ./words.bend as Words

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

# The specification's word addition is addition modulo 2^64 (FIPS 180-4
# section 3.2), with W{hi, lo} read as lo + 2^32 hi.
law spec_add_mod:
  for +a: T.Lane
  for +b: T.Lane
  {Words.value(FIPS.add(a, b)) == C.low(64n, Nat.add(Words.value(a), Words.value(b))) : Nat}
