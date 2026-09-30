import Base
import ./aes/gcm.bend as G

# AES-GCM authenticated encryption (NIST SP 800-38D, AES from FIPS 197):
# 96-bit (12-byte) nonces, 128-bit (16-byte) tags appended to the
# ciphertext. Bytes are U32 values below 256. A key or nonce of the wrong
# length gives None; decryption gives None when the tag does not match
# (compared in constant time with subtle.eq). Proved equal to the executable
# specification spec/crypto/aes/gcm.bend (proofs/crypto/aes/).

# AES-128-GCM: a 16-byte key. Returns ciphertext || tag.
def aes128_gcm_encrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  G.seal_key(G.schedule_of(16n, key), nonce, aad, pt)

# The plaintext of ciphertext || tag, or None.
def aes128_gcm_decrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  G.open_key(G.schedule_of(16n, key), nonce, aad, ct)

# AES-256-GCM: a 32-byte key.
def aes256_gcm_encrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  G.seal_key(G.schedule_of(32n, key), nonce, aad, pt)

def aes256_gcm_decrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  G.open_key(G.schedule_of(32n, key), nonce, aad, ct)
