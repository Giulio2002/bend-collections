import Base
import ../../../src/crypto/sha3/core.bend as C
import ../../../src/crypto/sha3/stream.bend as N
import ../../../spec/crypto/sha3.bend as FIPS
import ./conformance.bend as Conformance
import ./stream.bend as Stream
import ./laws.bend as Laws

# Gate for the SHA3-256 package: `bend proofs/crypto/sha3/proof.bend` prints
# ALL PROOFS CHECK when every law of laws.bend holds. The conformance is
# proved for every round count; SHA3-256 instantiates 24.

def Laws.sha3_256_correct(bytes):
  Equal.trans(List<&2, U32>, N.hash(bytes), C.keccak(bytes, 24n), FIPS.sha3_256(bytes),
    Stream.hash_correct(bytes), Conformance.keccak_correct(bytes, 24n))

def Laws.sha3_256_length(bytes):
  %Equal.sym(List<&2, U32>, N.hash(bytes), C.keccak(bytes, 24n), Stream.hash_correct(bytes)) :
    {List.length(&2, U32, _) == 32n : Nat}
  Conformance.digest_length(C.absorb(C.lanes(List.append(&2, U32, bytes,
    C.suffix(List.length(&2, U32, bytes)))), 24n, C.zero()))
