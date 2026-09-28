import Base
import ../../../spec/lib/common.bend as C
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

# The specification's reduction is x mod (2^130 - 5), for every x
# (2^130 written C.shift(130n, one) with one == 1, as the checker would
# expand a closed 2^130 in unary).
law modp_mod:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +x: Nat
  {R.modp(x) == Nat.mod(x, Nat.sub(C.shift(130n, one), 5n)) : Nat}

# The checked API: the tag for a 32-byte key, None for any other length.
law poly1305_valid:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, key), 32n) == True{} : Bool}
  {P.poly1305(key, msg) == Some{R.mac(key, msg)} : Maybe<&2, List<&2, U32>>}

law poly1305_invalid:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, key), 32n) == False{} : Bool}
  {P.poly1305(key, msg) == None{} : Maybe<&2, List<&2, U32>>}

# verify accepts the RFC tag under a 32-byte key ...
law verify_accepts:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, key), 32n) == True{} : Bool}
  {P.verify(key, msg, R.mac(key, msg)) == True{} : Bool}

# ... and rejects every other tag.
law verify_rejects:
  for +key: List<&2, U32>
  for +msg: List<&2, U32>
  for +tag: List<&2, U32>
  for h: {tag != R.mac(key, msg) : List<&2, U32>}
  {P.verify(key, msg, tag) == False{} : Bool}
