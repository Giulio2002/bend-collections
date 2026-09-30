import Base
import ../../../src/crypto/chacha/chacha20.bend as I
import ../../../spec/crypto/chacha.bend as R

# The ChaCha20 / HChaCha20 / XChaCha20 clauses of src/crypto/chacha/ against
# spec/crypto/chacha.bend (RFC 8439 sections 2.3-2.4,
# draft-irtf-cfrg-xchacha-03 sections 2.2-2.3). Proved in proof.bend, for
# every key, nonce, counter and byte list (lists of any length and any U32
# values). r is the number of double rounds: every clause stated with r holds
# for ChaCha20 (10), ChaCha12 (6) and ChaCha8 (4) alike.

# ---- the functions against the specification

# chacha20_block with r double rounds.
law block_rounds:
  for +r: Nat
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  {I.block_rounds(r, key, counter, nonce) == R.block_rounds(r, key, counter, nonce) : List<&2, U32>}

# chacha20_encrypt with r double rounds.
law encrypt_rounds:
  for +r: Nat
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  {I.encrypt_rounds(r, key, counter, nonce, plaintext) == R.encrypt_rounds(r, key, counter, nonce, plaintext) : List<&2, U32>}

# HChaCha20 with r double rounds, and at twenty rounds.
law hchacha_rounds:
  for +r: Nat
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  {I.hchacha_rounds(r, key, nonce) == R.hchacha_rounds(r, key, nonce) : List<&2, U32>}

law hchacha20:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  {I.hchacha20_unchecked(key, nonce) == R.hchacha20(key, nonce) : List<&2, U32>}

# XChaCha20.
law xencrypt:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  {I.xencrypt_unchecked(key, counter, nonce, plaintext) == R.xencrypt(key, counter, nonce, plaintext) : List<&2, U32>}

# ---- the checked API: Some(the specification) on the RFC lengths, None otherwise

law chacha20_block.valid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  {I.chacha20_block(key, counter, nonce) == Some{R.block(key, counter, nonce)} : Maybe<&2, List<&2, U32>>}

law chacha20_block.invalid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +h: {Bool.and(Nat.is_eq(List.length(&2, U32, key), 32n), Nat.is_eq(List.length(&2, U32, nonce), 12n)) == False{} : Bool}
  {I.chacha20_block(key, counter, nonce) == None{} : Maybe<&2, List<&2, U32>>}

law chacha20.valid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  {I.chacha20(key, counter, nonce, plaintext) == Some{R.encrypt(key, counter, nonce, plaintext)} : Maybe<&2, List<&2, U32>>}

law chacha20.invalid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  for +h: {Bool.and(Nat.is_eq(List.length(&2, U32, key), 32n), Nat.is_eq(List.length(&2, U32, nonce), 12n)) == False{} : Bool}
  {I.chacha20(key, counter, nonce, plaintext) == None{} : Maybe<&2, List<&2, U32>>}

law hchacha20.valid:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +hn: {List.length(&2, U32, nonce) == 16n : Nat}
  {I.hchacha20(key, nonce) == Some{R.hchacha20(key, nonce)} : Maybe<&2, List<&2, U32>>}

law hchacha20.invalid:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +h: {Bool.and(Nat.is_eq(List.length(&2, U32, key), 32n), Nat.is_eq(List.length(&2, U32, nonce), 16n)) == False{} : Bool}
  {I.hchacha20(key, nonce) == None{} : Maybe<&2, List<&2, U32>>}

law xchacha20.valid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +hn: {List.length(&2, U32, nonce) == 24n : Nat}
  {I.xchacha20(key, counter, nonce, plaintext) == Some{R.xencrypt(key, counter, nonce, plaintext)} : Maybe<&2, List<&2, U32>>}

law xchacha20.invalid:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  for +h: {Bool.and(Nat.is_eq(List.length(&2, U32, key), 32n), Nat.is_eq(List.length(&2, U32, nonce), 24n)) == False{} : Bool}
  {I.xchacha20(key, counter, nonce, plaintext) == None{} : Maybe<&2, List<&2, U32>>}

# ---- properties

# Decryption is encryption: applying the cipher twice is the identity.
law involution:
  for +r: Nat
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  {I.encrypt_rounds(r, key, counter, nonce, I.encrypt_rounds(r, key, counter, nonce, plaintext)) == plaintext : List<&2, U32>}

law xinvolution:
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  {I.xencrypt_unchecked(key, counter, nonce, I.xencrypt_unchecked(key, counter, nonce, plaintext)) == plaintext : List<&2, U32>}

# The ciphertext is as long as the plaintext.
law encrypt_length:
  for +r: Nat
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  for +plaintext: List<&2, U32>
  {List.length(&2, U32, I.encrypt_rounds(r, key, counter, nonce, plaintext)) == List.length(&2, U32, plaintext) : Nat}

# The block function's output has 64 bytes, HChaCha20's 32.
law block_length:
  for +r: Nat
  for +key: List<&2, U32>
  for +counter: U32
  for +nonce: List<&2, U32>
  {List.length(&2, U32, R.block_rounds(r, key, counter, nonce)) == 64n : Nat}

law hchacha_length:
  for +r: Nat
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  {List.length(&2, U32, R.hchacha_rounds(r, key, nonce)) == 32n : Nat}
