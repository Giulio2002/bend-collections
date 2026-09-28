import Base
import ../../../src/crypto/sha512/core.bend as C
import ./conformance.bend as Conformance
import ./words.bend as Words
import ./laws.bend as Laws

# Gate for the SHA-512 package: `bend proofs/crypto/sha512/proof.bend` prints
# ALL PROOFS CHECK when every law of laws.bend holds.

def Laws.sha512_correct(bytes):
  Conformance.sha512_correct(bytes)

def Laws.sha512_length(bytes):
  Conformance.digest_length(C.blocks(C.lanes(List.append(&2, U32, bytes,
    C.suffix(List.length(&2, U32, bytes)))), 64n, C.round_constants(), C.initial()))

def Laws.spec_add_mod(a, b):
  Words.add_value(a, b)
