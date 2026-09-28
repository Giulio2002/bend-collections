import Base
import ../../../src/crypto/aead.bend as A
import ../../../src/crypto/aead/chacha20poly1305.bend as CP
import ../../../spec/crypto/chacha20poly1305.bend as R

# The clauses of the AEAD facade src/crypto/aead.bend (proved in proof.bend,
# one case per algorithm). hk / hn: the key and nonce have the algorithm's
# lengths.

# ---- each algorithm is its specification (for keys and nonces of any length)

law chacha20poly1305.seal:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.CHACHA20_POLY1305{}, key, nonce, aad, pt) == R.seal(key, nonce, aad, pt) : List<&2, U32>}

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
  {A.seal(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt) == R.xseal(key, nonce, aad, pt) : List<&2, U32>}

law xchacha20poly1305.open:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {A.open(A.XCHACHA20_POLY1305{}, key, nonce, aad, data) == R.xopen(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

# The per-algorithm checked API agrees with the facade.
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
  {A.encrypt(alg, key, nonce, aad, pt) == Some{A.seal(alg, key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

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
  {A.decrypt(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

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
  for ne: {t != A.expected_tag(alg, key, nonce, aad, ct) : List<&2, U32>}
  {A.decrypt(alg, key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

# The sealed message is the ciphertext followed by the expected tag.
law seal_layout:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  exs ct: List<&2, U32>
  {A.seal(alg, key, nonce, aad, pt) == List.append(&2, U32, ct, A.expected_tag(alg, key, nonce, aad, ct)) : List<&2, U32>}
