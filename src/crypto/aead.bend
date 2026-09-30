import Base
import ./aead/chacha20poly1305.bend as CP
import ./aesgcm.bend as GCM

# Authenticated encryption with associated data (RFC 5116 shape).
#
#   encrypt(alg, key, nonce, aad, plaintext) -> Maybe(ciphertext || tag)
#   decrypt(alg, key, nonce, aad, ciphertext || tag) -> Maybe(plaintext)
#
# Bytes are U32 values < 256. Every algorithm has a 16-byte tag appended to
# the ciphertext. encrypt returns None unless the key and nonce have the
# algorithm's lengths (key_size, nonce_size); decrypt also returns None for
# an input shorter than the tag and whenever the tag is not the one computed
# over aad and ciphertext (a forgery, a wrong key/nonce/aad, a modified
# ciphertext); no plaintext is returned then.
#
#   algorithm            key  nonce  tag   standard
#   CHACHA20_POLY1305    32   12     16    RFC 8439 2.8
#   XCHACHA20_POLY1305   32   24     16    draft-irtf-cfrg-xchacha-03
#   AES_128_GCM          16   12     16    FIPS 197 + SP 800-38D
#   AES_256_GCM          32   12     16    FIPS 197 + SP 800-38D
#
# Adding an algorithm: a constructor of Alg, its row in key_size and
# nonce_size, and its case in seal and open (the per-algorithm functions,
# which may do their own length checks); encrypt and decrypt check the
# lengths and dispatch, and the laws in proofs/crypto/aead/laws.bend are
# proved by one case per algorithm.
#
# Proved (proofs/crypto/aead/): each algorithm equals its specification
# (spec/crypto/chacha20poly1305.bend, spec/crypto/aes/gcm.bend),
# decrypt(encrypt(x)) == Some(x) for every key, nonce, aad and plaintext of
# the right lengths, and decrypt rejects ciphertext || t for every 16-byte t
# other than the tag the specification computes. Constant time is not
# provable in Bend (no timing model); the code does not branch or index on
# secret bytes except for the final accept/reject.

type Alg is Data:
  CHACHA20_POLY1305{}
  XCHACHA20_POLY1305{}
  AES_128_GCM{}
  AES_256_GCM{}

def key_size(alg: Alg) -> Nat:
  match alg:
    case CHACHA20_POLY1305{}: 32n
    case XCHACHA20_POLY1305{}: 32n
    case AES_128_GCM{}: 16n
    case AES_256_GCM{}: 32n

def nonce_size(alg: Alg) -> Nat:
  match alg:
    case CHACHA20_POLY1305{}: 12n
    case XCHACHA20_POLY1305{}: 24n
    case AES_128_GCM{}: 12n
    case AES_256_GCM{}: 12n

def tag_size() -> Nat:
  16n

# ciphertext || tag (encrypt checks the key and nonce lengths first).
def seal(alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match alg:
    case CHACHA20_POLY1305{}: Some{CP.seal(key, nonce, aad, pt)}
    case XCHACHA20_POLY1305{}: Some{CP.xseal(key, nonce, aad, pt)}
    case AES_128_GCM{}: GCM.aes128_gcm_encrypt(key, nonce, aad, pt)
    case AES_256_GCM{}: GCM.aes256_gcm_encrypt(key, nonce, aad, pt)

# The plaintext of ciphertext || tag, or None (decrypt checks the lengths first).
def open(alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match alg:
    case CHACHA20_POLY1305{}: CP.open(key, nonce, aad, data)
    case XCHACHA20_POLY1305{}: CP.xopen(key, nonce, aad, data)
    case AES_128_GCM{}: GCM.aes128_gcm_decrypt(key, nonce, aad, data)
    case AES_256_GCM{}: GCM.aes256_gcm_decrypt(key, nonce, aad, data)

def valid(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, U32, key), key_size(alg)), Nat.is_eq(List.length(&2, U32, nonce), nonce_size(alg)))

def when_open(ok: Bool, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: r
    case False{}: None{}

def encrypt(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when_open(valid(alg, key, nonce), seal(alg, key, nonce, aad, pt))

def decrypt(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when_open(valid(alg, key, nonce), open(alg, key, nonce, aad, data))
