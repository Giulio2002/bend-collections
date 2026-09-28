import Base
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../../spec/crypto/poly1305.bend as R

# The Poly1305 clauses (proved in proof.bend).

# The implementation's tag is the RFC 8439 tag, for every key and message
# (keys of other lengths than 32 included: both read missing bytes as absent).
law mac_correct:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {P.mac(key, msg) == R.mac(key, msg) : List<&2, U32>}

# The tag has 16 bytes.
law mac_length:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  {List.length(&2, U32, R.mac(key, msg)) == 16n : Nat}
