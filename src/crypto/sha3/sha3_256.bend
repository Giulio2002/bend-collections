import Base
import ./stream.bend as Stream

# SHA3-256 (FIPS 202) on the Keccak-f[1600] permutation of src/crypto/keccak.
# It differs from Ethereum's Keccak-256 (src/crypto/keccak/keccak.bend) only in
# the domain padding: SHA-3 appends 0x06 where Keccak-256 appends 0x01.
# Bytes are U32 values, each < 256; the digest is 32 bytes. Proved equal to
# spec/crypto/sha3.bend for every input: proofs/crypto/sha3/laws.bend.
def sha3_256(bytes: List<&2, U32>) -> List<&2, U32>:
  Stream.hash(bytes)
