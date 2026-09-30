import Base
import ../../../src/crypto/mac.bend as MAC
import ../../../spec/crypto/hmac.bend as Spec
import ../../../spec/crypto/subtle.bend as SubtleSpec

# The clauses of src/crypto/mac.bend (HMAC-SHA256), proved in proof.bend.
# Every clause is for every key, message and tag (any U32 lists).

# sign is RFC 2104 / FIPS 198-1 HMAC over FIPS 180-4 SHA-256.
law Sign.correct:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {MAC.sign(key, msg) == Spec.hmac(key, msg) : List<&2, U32>}

# Every tag is 32 bytes.
law Sign.length:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {List.length(&2, U32, MAC.sign(key, msg)) == 32n : Nat}

# verify is the reference comparison of the tag with the specified HMAC.
law Verify.value:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +tag: List<&2, U32>
  {MAC.verify(key, msg, tag) == SubtleSpec.equal(Spec.hmac(key, msg), tag) : Bool}

# The tag of a message verifies.
law Verify.accepts:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {MAC.verify(key, msg, MAC.sign(key, msg)) == True{} : Bool}

# A tag that verifies is the tag.
law Verify.sound:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +tag: List<&2, U32>
  for +h: {MAC.verify(key, msg, tag) == True{} : Bool}
  {tag == MAC.sign(key, msg) : List<&2, U32>}

# Any other tag is rejected.
law Verify.rejects:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +tag: List<&2, U32>
  for ne: {tag != MAC.sign(key, msg) : List<&2, U32>}
  {MAC.verify(key, msg, tag) == False{} : Bool}
