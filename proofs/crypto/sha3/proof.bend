import Base
import ../../../src/crypto/sha3/core.bend as C
import ./conformance.bend as Conformance
import ./laws.bend as Laws

# Gate for the SHA3-256 package: `bend proofs/crypto/sha3/proof.bend` prints
# ALL PROOFS CHECK when every law of laws.bend holds. The conformance is
# proved for every round count; SHA3-256 instantiates 24.

def Laws.sha3_256_correct(bytes):
  Conformance.keccak_correct(bytes, 24n)

def Laws.sha3_256_length(bytes):
  Conformance.digest_length(C.absorb(C.lanes(List.append(&2, U32, bytes,
    C.suffix(List.length(&2, U32, bytes)))), 24n, C.zero()))
