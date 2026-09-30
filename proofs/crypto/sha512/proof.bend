import Base
import ../../../src/crypto/sha512/core.bend as C
import ../../../src/crypto/sha512/stream.bend as N
import ../../../spec/crypto/sha512.bend as FIPS
import ./conformance.bend as Conformance
import ./words.bend as Words
import ./stream.bend as Stream
import ./laws.bend as Laws

# Gate for the SHA-512 package: `bend proofs/crypto/sha512/proof.bend` prints
# ALL PROOFS CHECK when every law of laws.bend holds.

def Laws.sha512_correct(bytes):
  Equal.trans(List<&2, U32>, N.hash(bytes), C.sha512(bytes), FIPS.sha512_bytes(bytes),
    Stream.hash_correct(bytes), Conformance.sha512_correct(bytes))

def Laws.sha512_length(bytes):
  %Equal.sym(List<&2, U32>, N.hash(bytes), C.sha512(bytes), Stream.hash_correct(bytes)) :
    {List.length(&2, U32, _) == 64n : Nat}
  Conformance.digest_length(C.blocks(C.lanes(List.append(&2, U32, bytes,
    C.suffix(List.length(&2, U32, bytes)))), 64n, C.round_constants(), C.initial()))

def Laws.spec_add_mod(a, b):
  Words.add_value(a, b)
