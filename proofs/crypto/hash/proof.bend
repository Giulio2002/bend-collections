import Base
import ../../../src/crypto/sha/state.bend as S256
import ../../../src/crypto/sha/core.bend as C256
import ../../../src/crypto/sha/sha256.bend as SHA256
import ../../../src/crypto/sha512/core.bend as C512
import ../../../src/crypto/sha3/core.bend as C3
import ../../../src/crypto/hash.bend as Hash
import ../sha/conformance.bend as SC
import ../sha/laws.bend as SL
import ../sha/correctness.bend as SCorr
import ../sha512/conformance.bend as S512
import ../sha3/conformance.bend as S3
import ./lists.bend as L
import ./incremental.bend as I
import ./laws.bend as Laws

# Gate for src/crypto/hash.bend: `bend proofs/crypto/hash/proof.bend` prints
# ALL PROOFS CHECK when every clause of laws.bend holds.

def Laws.Sha256.value(bytes):
  SL.sha256_bytes_correct(bytes)

def Laws.Sha512.value(bytes):
  S512.sha512_correct(bytes)

def Laws.Sha3_256.value(bytes):
  S3.keccak_correct(bytes, 24n)

def Laws.Sha256.length(bytes):
  SL.sha256_bytes_length(bytes)

def Laws.Sha512.length(bytes):
  S512.digest_length(C512.blocks(C512.lanes(List.append(&2, U32, bytes,
    C512.suffix(List.length(&2, U32, bytes)))), 64n, C512.round_constants(), C512.initial()))

def Laws.Sha3_256.length(bytes):
  S3.digest_length(C3.absorb(C3.lanes(List.append(&2, U32, bytes,
    C3.suffix(List.length(&2, U32, bytes)))), 24n, C3.zero()))

# The one-shot SHA-256 is its block loop over the padded message (the SHA-256
# package's stream_correct, with nothing hashed before).
law oneshot256:
  for +m: List<&2, U32>
  {Hash.sha256(m) == SHA256.digest_bytes(C256.digest(C256.block_bytes(List.append(&2, U32, m,
    C256.suffix(List.length(&2, U32, m))), 48n, C256.round_constants(), C256.initial()))) : List<&2, U32>}

def oneshot256(m):
  %L.add_zero(List.length(&2, U32, m)) :
    {Hash.sha256(m) == SHA256.digest_bytes(C256.digest(C256.block_bytes(List.append(&2, U32, m,
      C256.suffix(_)), 48n, C256.round_constants(), C256.initial()))) : List<&2, U32>}
  Equal.cong(S256.State, List<&2, U32>, t => SHA256.digest_bytes(C256.digest(t)),
    C256.stream(m, 0n, 48n, C256.initial()),
    C256.block_bytes(List.append(&2, U32, m, C256.suffix(Nat.add(List.length(&2, U32, m), 0n))),
      48n, C256.round_constants(), C256.initial()),
    SC.stream_correct(m, 0n, 48n, C256.initial()))

def Laws.Incremental.sha256(chunks):
  +m = List.concat(&2, U32, chunks)
  Equal.trans(List<&2, U32>,
    Hash.digest(Hash.update_all(Hash.new_sha256(), chunks)),
    SHA256.digest_bytes(C256.digest(C256.block_bytes(List.append(&2, U32, m,
      C256.suffix(List.length(&2, U32, m))), 48n, C256.round_constants(), C256.initial()))),
    Hash.sha256(m),
    I.incremental256(chunks),
    Equal.sym(List<&2, U32>, Hash.sha256(m), SHA256.digest_bytes(C256.digest(C256.block_bytes(List.append(&2, U32, m,
      C256.suffix(List.length(&2, U32, m))), 48n, C256.round_constants(), C256.initial()))), oneshot256(m)))

def Laws.Incremental.sha512(chunks):
  I.incremental512(chunks)

def Laws.Incremental.sha3_256(chunks):
  I.incremental3(chunks)

def Laws.Split.sha256(a, b):
  %L.append_nil(b) :
    {Hash.digest(Hash.update(Hash.update(Hash.new_sha256(), a), b)) == Hash.sha256(List.append(&2, U32, a, _)) : List<&2, U32>}
  Laws.Incremental.sha256([a, b])

def Laws.Split.sha512(a, b):
  %L.append_nil(b) :
    {Hash.digest(Hash.update(Hash.update(Hash.new_sha512(), a), b)) == Hash.sha512(List.append(&2, U32, a, _)) : List<&2, U32>}
  Laws.Incremental.sha512([a, b])

def Laws.Split.sha3_256(a, b):
  %L.append_nil(b) :
    {Hash.digest(Hash.update(Hash.update(Hash.new_sha3_256(), a), b)) == Hash.sha3_256(List.append(&2, U32, a, _)) : List<&2, U32>}
  Laws.Incremental.sha3_256([a, b])
