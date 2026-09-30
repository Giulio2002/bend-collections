import Base
import ../chacha/chacha20.bend as CH
import ../poly1305/poly1305.bend as P
import ../subtle.bend as S

# ChaCha20-Poly1305 (RFC 8439 section 2.8) and XChaCha20-Poly1305
# (draft-irtf-cfrg-xchacha-03), over byte lists (U32 values < 256).
#
#   encrypt(key, nonce, aad, plaintext) -> Some(ciphertext || tag)
#   decrypt(key, nonce, aad, ciphertext || tag) -> Some(plaintext)
#
# Keys have 32 bytes, nonces 12 (ChaCha20-Poly1305) or 24 (XChaCha20-
# Poly1305), tags 16. Both functions return None for other key or nonce
# lengths; decrypt returns None for inputs shorter than a tag and whenever
# the tag differs from the one computed over aad and ciphertext (compared
# with the constant-time Subtle.eq, before any plaintext is produced).
# Bend has no timing model: constant time is a property of the code's shape
# (no branch or index on secret bytes; only the final accept/reject), not a
# proved fact.

# poly1305_key_gen: the first 32 bytes of the block with counter 0.
def poly_key(key: List<&2, U32>, nonce: List<&2, U32>) -> List<&2, U32>:
  CH.take(32n, CH.block_rounds(10n, key, 0, nonce))

# The tag over aad | pad16(aad) | ct | pad16(ct) | le64(len aad) |
# le64(len ct), computed by src/crypto/poly1305 without building that list.
def tag(+key: List<&2, U32>, +nonce: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> List<&2, U32>:
  P.mac_aead(poly_key(key, nonce), aad, ct)

# chacha20_encrypt(key, 1, nonce, plaintext).
def encrypt_ct(key: List<&2, U32>, nonce: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  CH.encrypt_rounds(10n, key, 1, nonce, pt)

# ciphertext || tag, without length checks.
def seal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  +ct = encrypt_ct(key, nonce, pt)
  List.append(&2, U32, ct, tag(key, nonce, aad, ct))

def open_tag(ok: Bool, +key: List<&2, U32>, +nonce: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{CH.encrypt_rounds(10n, key, 1, nonce, ct)}
    case False{}: None{}

def open_split(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>, +t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open_tag(S.eq(t, tag(key, nonce, aad, ct)), key, nonce, ct)

# xs without its last len(lead) bytes, and those bytes, for lead = xs past
# its first 16 bytes (one pass each, no length computed).
def body(lead: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  match lead xs:
    case l <> lt x <> dt: x <> body(lt, dt)
    case _ _: Nil{}

def tail(lead: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  match lead xs:
    case l <> lt x <> dt: tail(lt, dt)
    case _ _: xs

# The plaintext of ciphertext || tag, without key/nonce length checks
# (None for an input shorter than a tag).
def open(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match data:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      open_split(key, nonce, aad, body(rest, data), tail(rest, data))
    case _: None{}

# XChaCha20-Poly1305: the HChaCha20 subkey of nonce[0..16] and the nonce
# 0x00000000 || nonce[16..24].
def xkey(key: List<&2, U32>, nonce: List<&2, U32>) -> List<&2, U32>:
  CH.hchacha20_unchecked(key, CH.take(16n, nonce))

def xnonce(nonce: List<&2, U32>) -> List<&2, U32>:
  0 <> 0 <> 0 <> 0 <> CH.skip(16n, nonce)

def xseal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  seal(xkey(key, nonce), xnonce(nonce), aad, pt)

def xopen(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open(xkey(key, nonce), xnonce(nonce), aad, data)

# ---------------------------------------------------------------- checked API

def lengths_ok(+key: List<&2, U32>, +nonce: List<&2, U32>, n: Nat) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, U32, key), 32n), Nat.is_eq(List.length(&2, U32, nonce), n))

def when(ok: Bool, x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{x}
    case False{}: None{}

def when_open(ok: Bool, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: r
    case False{}: None{}

def encrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(lengths_ok(key, nonce, 12n), seal(key, nonce, aad, pt))

def decrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when_open(lengths_ok(key, nonce, 12n), open(key, nonce, aad, data))

def xencrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(lengths_ok(key, nonce, 24n), xseal(key, nonce, aad, pt))

def xdecrypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when_open(lengths_ok(key, nonce, 24n), xopen(key, nonce, aad, data))
