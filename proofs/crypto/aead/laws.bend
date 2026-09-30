import Base
import ../../../src/crypto/aead.bend as A
import ../../../src/crypto/aead/chacha20poly1305.bend as CP
import ../../../spec/crypto/chacha.bend as RC
import ../../../spec/crypto/chacha20poly1305.bend as R
import ../../../spec/crypto/aes/gcm.bend as G

# The clauses of the AEAD facade src/crypto/aead.bend (proved in proof.bend,
# one case per algorithm). hk / hn: the key and nonce have the algorithm's
# lengths.

# The tag the specification computes over ciphertext ct: decrypt accepts
# ct || t exactly for this t.
def expected_tag(alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  match alg:
    case A.CHACHA20_POLY1305{}: R.tag(key, nonce, aad, ct)
    case A.XCHACHA20_POLY1305{}: R.tag(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, ct)
    case A.AES_128_GCM{}: G.aes_tag(key, nonce, aad, ct)
    case A.AES_256_GCM{}: G.aes_tag(key, nonce, aad, ct)

# decrypt applied to what encrypt returned (None stays None).
def decrypt_sealed(+alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{c}: A.decrypt(alg, key, nonce, aad, c)

# ---- each algorithm is its specification

law chacha20poly1305.seal:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.CHACHA20_POLY1305{}, key, nonce, aad, pt) == Some{R.seal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

law chacha20poly1305.open:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {A.open(A.CHACHA20_POLY1305{}, key, nonce, aad, data) == R.open(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

law xchacha20poly1305.seal:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt) == Some{R.xseal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

law xchacha20poly1305.open:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {A.open(A.XCHACHA20_POLY1305{}, key, nonce, aad, data) == R.xopen(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

law aes128gcm.seal:
  for +key: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.AES_128_GCM{}, key, nonce, aad, pt) == Some{G.aes_seal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

law aes128gcm.open:
  for +key: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {A.open(A.AES_128_GCM{}, key, nonce, aad, data) == G.aes_open(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

law aes256gcm.seal:
  for +key: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.AES_256_GCM{}, key, nonce, aad, pt) == Some{G.aes_seal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

law aes256gcm.open:
  for +key: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {A.open(A.AES_256_GCM{}, key, nonce, aad, data) == G.aes_open(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

# The per-algorithm checked ChaCha20-Poly1305 API agrees with the facade.
law chacha20poly1305.encrypt:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {CP.encrypt(key, nonce, aad, pt) == A.encrypt(A.CHACHA20_POLY1305{}, key, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}

law chacha20poly1305.decrypt:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {CP.decrypt(key, nonce, aad, data) == A.decrypt(A.CHACHA20_POLY1305{}, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

law xchacha20poly1305.encrypt:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {CP.xencrypt(key, nonce, aad, pt) == A.encrypt(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}

law xchacha20poly1305.decrypt:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {CP.xdecrypt(key, nonce, aad, data) == A.decrypt(A.XCHACHA20_POLY1305{}, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

# ---- the checked API

law encrypt.valid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {A.encrypt(alg, key, nonce, aad, pt) == A.seal(alg, key, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}

law encrypt.invalid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +h: {A.valid(alg, key, nonce) == False{} : Bool}
  {A.encrypt(alg, key, nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}

law decrypt.valid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {A.decrypt(alg, key, nonce, aad, data) == A.open(alg, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

law decrypt.invalid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +h: {A.valid(alg, key, nonce) == False{} : Bool}
  {A.decrypt(alg, key, nonce, aad, data) == None{} : Maybe<&2, List<&2, U32>>}

# ---- the AEAD properties

# decrypt(encrypt(x)) == Some(x).
law roundtrip:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {decrypt_sealed(alg, key, nonce, aad, A.encrypt(alg, key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

# ciphertext || t is rejected for every 16-byte t other than the tag of the
# ciphertext under this key, nonce and aad.
law forgery:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != expected_tag(alg, key, nonce, aad, ct) : List<&2, U32>}
  {A.decrypt(alg, key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

# What encrypt returns is a ciphertext followed by its expected tag.
law seal_layout:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  exs ct: List<&2, U32>
  {A.encrypt(alg, key, nonce, aad, pt) == Some{List.append(&2, U32, ct, expected_tag(alg, key, nonce, aad, ct))} : Maybe<&2, List<&2, U32>>}

# Decryption is sound: whatever decrypt accepts is exactly what encrypt
# produces for the returned plaintext (so every accepted input is the honest
# ciphertext of its plaintext under this key, nonce and aad).
law decrypt_sound:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +p: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  for +h: {A.decrypt(alg, key, nonce, aad, data) == Some{p} : Maybe<&2, List<&2, U32>>}
  {A.encrypt(alg, key, nonce, aad, p) == Some{data} : Maybe<&2, List<&2, U32>>}
