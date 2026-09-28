import Base
import ./aead/chacha20poly1305.bend as CP

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
# ciphertext), before any plaintext is produced.
#
#   algorithm            key  nonce  tag   standard
#   CHACHA20_POLY1305    32   12     16    RFC 8439 2.8
#   XCHACHA20_POLY1305   32   24     16    draft-irtf-cfrg-xchacha-03
#
# Adding an algorithm: a constructor of Alg, its row in key_size and
# nonce_size, and its case in seal, open and expected_tag (the unchecked
# functions); encrypt and decrypt dispatch through those, and the laws in
# proofs/crypto/aead/laws.bend are proved by one case per algorithm.
#
# Proved (proofs/crypto/aead/): each algorithm equals its specification
# (spec/crypto/chacha20poly1305.bend), decrypt(encrypt(x)) == Some(x) for
# every key, nonce, aad and plaintext of the right lengths, and decrypt
# rejects every ciphertext || tag whose tag is not the expected one.
# Constant time is not provable in Bend (no timing model); the code does not
# branch or index on secret bytes except for the final accept/reject.

type Alg is Data:
  CHACHA20_POLY1305{}
  XCHACHA20_POLY1305{}

def key_size(alg: Alg) -> Nat:
  match alg:
    case CHACHA20_POLY1305{}: 32n
    case XCHACHA20_POLY1305{}: 32n

def nonce_size(alg: Alg) -> Nat:
  match alg:
    case CHACHA20_POLY1305{}: 12n
    case XCHACHA20_POLY1305{}: 24n

def tag_size() -> Nat:
  16n

# ciphertext || tag, for keys and nonces of any length (encrypt checks them).
def seal(alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  match alg:
    case CHACHA20_POLY1305{}: CP.seal(key, nonce, aad, pt)
    case XCHACHA20_POLY1305{}: CP.xseal(key, nonce, aad, pt)

# The plaintext of ciphertext || tag, or None (decrypt checks the lengths).
def open(alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match alg:
    case CHACHA20_POLY1305{}: CP.open(key, nonce, aad, data)
    case XCHACHA20_POLY1305{}: CP.xopen(key, nonce, aad, data)

# The tag decrypt expects after the ciphertext ct.
def expected_tag(alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  match alg:
    case CHACHA20_POLY1305{}: CP.tag(key, nonce, aad, ct)
    case XCHACHA20_POLY1305{}: CP.tag(CP.xkey(key, nonce), CP.xnonce(nonce), aad, ct)

def valid(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, U32, key), key_size(alg)), Nat.is_eq(List.length(&2, U32, nonce), nonce_size(alg)))

def when(ok: Bool, x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{x}
    case False{}: None{}

def when_open(ok: Bool, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: r
    case False{}: None{}

def encrypt(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(valid(alg, key, nonce), seal(alg, key, nonce, aad, pt))

def decrypt(+alg: Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when_open(valid(alg, key, nonce), open(alg, key, nonce, aad, data))
