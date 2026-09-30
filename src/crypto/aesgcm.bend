import Base
import ./aes/gcm.bend as G
import ./aes/aes.bend as A
import ./aes/fast.bend as F

# AES-GCM authenticated encryption (NIST SP 800-38D, AES from FIPS 197):
# 96-bit (12-byte) nonces, 128-bit (16-byte) tags appended to the
# ciphertext. Bytes are U32 values below 256. A key or nonce of the wrong
# length gives None; decryption gives None when the tag does not match
# (compared in constant time with subtle.eq). Proved equal to the executable
# specification spec/crypto/aes/gcm.bend (proofs/crypto/aes/).

# AES-128-GCM: a 16-byte key. Returns ciphertext || tag.
def nonce_of(n: List<&2, U32>) -> Maybe<&2, F.Nonce>:
  match n:
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      Some{F.N{F.le32(n0, n1, n2, n3), F.le32(n4, n5, n6, n7), F.le32(n8, n9, n10, n11)}}
    case _: None{}

def seal_with(m: Maybe<&2, A.Schedule>, nn: Maybe<&2, F.Nonce>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m nn:
    case Some{s} Some{n}: Some{F.seal(F.keys_of(s), n, aad, pt)}
    case _ _: None{}

def open_with(m: Maybe<&2, A.Schedule>, nn: Maybe<&2, F.Nonce>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m nn:
    case Some{s} Some{n}: F.open(F.keys_of(s), n, aad, ct)
    case _ _: None{}

def aes128_gcm_encrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  seal_with(G.schedule_of(16n, key), nonce_of(nonce), aad, pt)

def aes128_gcm_decrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open_with(G.schedule_of(16n, key), nonce_of(nonce), aad, ct)

def aes256_gcm_encrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  seal_with(G.schedule_of(32n, key), nonce_of(nonce), aad, pt)

def aes256_gcm_decrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open_with(G.schedule_of(32n, key), nonce_of(nonce), aad, ct)
