#!/usr/bin/env python3
"""Generate proofs/crypto/aes/laws.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

ns=['n%d'%i for i in range(12)]
bs=['b%d'%i for i in range(16)]
ts=['t%d'%i for i in range(16)]
L=lambda v: '[%s]' % ', '.join(v)
NL=L(ns)
NW='T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}'
NP='\n'.join('  for +%s: U32' % n for n in ns)
BP='\n'.join('  for +%s: U32' % n for n in bs)
TP='\n'.join('  for +%s: U32' % n for n in ts)
laws = '''import Base
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/sbox.bend as B
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as GI
import ../../../src/crypto/aesgcm.bend as GCM
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G

# The clauses of the AES / AES-GCM contract (docs/CRYPTO_CONTRACTS.md),
# stated over the public functions and the executable specifications
# spec/crypto/aes/{aes,gcm}.bend. Proved in proof.bend.

# One block with an optional expanded key (the byte API in one call).
def block_with(m: Maybe<&2, A.Schedule>, block: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      A.encrypt_block(s, block)

# Decrypt what an encryption returned (None stays None).
def open128(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{ct}:
      GCM.aes128_gcm_decrypt(key, nonce, aad, ct)

def open256(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{ct}:
      GCM.aes256_gcm_decrypt(key, nonce, aad, ct)

# ---- AES (FIPS 197) ----

# The constant-time S-box circuit is FIPS 197's S-box (the inverse in
# GF(2^8), {00} to {00}, then the affine map), on every input.
law Sbox.value:
  for +x: U32
  {B.sbox(x) == S.sbox(x) : U32}

# The specification's inverse (a^254) is the multiplicative inverse of
# FIPS 197 section 4.4: a * a^-1 = {01} for every nonzero byte, and {00}
# goes to {00} (5.1.1); so S.sbox is "inverse, then affine map".
law Inverse.unit:
  for +x: U32
  for +h: {U32.is_eq(U32.and(255, x), 0) == False{} : Bool}
  {S.mul(x, S.inverse(x)) == 1 : U32}

law Inverse.zero:
  {S.inverse(0) == 0 : U32}

# The implementation's cipher with its expanded key is FIPS 197's Cipher
# with KeyExpansion, for every Nk, Nr, key and state.
law Cipher.value:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +s: T.State
  {A.encrypt(nk, nr, key, s) == S.encrypt(nk, nr, key, s) : T.State}

# The byte API: a key of 16, 24 or 32 bytes encrypts a 16-byte block with
# AES under the key's Nk = length/4 and Nr = Nk + 6 (FIPS 197 Figure 4).
law Block.value:
  for +key: List<&2, U32>
  for +h: {A.valid_length(List.length(&2, U32, key)) == True{} : Bool}
%s
  {block_with(A.expand_key(key), %s) == Some{S.bytes_of(S.aes(key, S.state_of(%s)))} : Maybe<&2, List<&2, U32>>}

# A 16-, 24-, 32-byte key is AES-128 (Nk = 4, Nr = 10), AES-192 (6, 12),
# AES-256 (8, 14).
law Block.aes128:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  {S.nk(key) == 4n : Nat}

law Block.aes192:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 24n : Nat}
  {S.nk(key) == 6n : Nat}

law Block.aes256:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  {S.nk(key) == 8n : Nat}

# ---- GCM (SP 800-38D) ----

# The implementation's GCM-AE / GCM-AD, for every expanded key, 96-bit
# nonce, AAD and input.
law Gcm.seal:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
%s
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GI.seal_core(A.Schedule{nr, A.expand(nk, nr, key)}, %s, aad, pt) == G.seal(nk, nr, key, %s, aad, pt) : List<&2, U32>}

law Gcm.open:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
%s
  for +aad: List<&2, U32>
  for +input: List<&2, U32>
  {GI.open_core(A.Schedule{nr, A.expand(nk, nr, key)}, %s, aad, input) == G.open(nk, nr, key, %s, aad, input) : Maybe<&2, List<&2, U32>>}

# AEAD correctness of the specification: opening the sealed message gives
# it back; C || T with T other than the tag of C is rejected.
law Aead.roundtrip:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +iv: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {G.open(nk, nr, key, iv, aad, G.seal(nk, nr, key, iv, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

law Aead.forgery:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +iv: List<&2, U32>
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
%s
  for ne: {%s != G.tag(nk, nr, key, iv, aad, c) : List<&2, U32>}
  {G.open(nk, nr, key, iv, aad, List.append(&2, U32, c, %s)) == None{} : Maybe<&2, List<&2, U32>>}
''' % (BP, L(bs), L(bs), NP, NW, NL, NP, NW, NL, TP, L(ts), L(ts))
for (w, nk, nr, name) in [(16, 4, 10, '128'), (32, 8, 14, '256')]:
    laws += '''
# ---- the AES-%s-GCM API (src/crypto/aesgcm.bend) ----

law Api%s.encrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == %dn : Nat}
%s
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes%s_gcm_encrypt(key, %s, aad, pt) == Some{G.aes_seal(key, %s, aad, pt)} : Maybe<&2, List<&2, U32>>}

law Api%s.decrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == %dn : Nat}
%s
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes%s_gcm_decrypt(key, %s, aad, ct) == G.aes_open(key, %s, aad, ct) : Maybe<&2, List<&2, U32>>}

# decrypt(encrypt(x)) == Some(x).
law Api%s.roundtrip:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == %dn : Nat}
%s
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {open%s(key, %s, aad, GCM.aes%s_gcm_encrypt(key, %s, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

# A wrong tag gives None.
law Api%s.forgery:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == %dn : Nat}
%s
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
%s
  for ne: {%s != G.aes_tag(key, %s, aad, c) : List<&2, U32>}
  {GCM.aes%s_gcm_decrypt(key, %s, aad, List.append(&2, U32, c, %s)) == None{} : Maybe<&2, List<&2, U32>>}

# A key of another length is rejected.
law Api%s.bad_key:
  for +key: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, key), %dn) == False{} : Bool}
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes%s_gcm_encrypt(key, nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}

law Api%s.bad_key_open:
  for +key: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, key), %dn) == False{} : Bool}
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes%s_gcm_decrypt(key, nonce, aad, ct) == None{} : Maybe<&2, List<&2, U32>>}

# A nonce other than 12 bytes is rejected.
law Api%s.bad_nonce:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes%s_gcm_encrypt(key, nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}

law Api%s.bad_nonce_open:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes%s_gcm_decrypt(key, nonce, aad, ct) == None{} : Maybe<&2, List<&2, U32>>}
''' % (name, name, w, NP, name, NL, NL,
       name, w, NP, name, NL, NL,
       name, w, NP, name, NL, name, NL,
       name, w, NP, TP, L(ts), NL, name, NL, L(ts),
       name, w, name, name, w, name, name, name, name, name)
open('proofs/crypto/aes/laws.bend','w').write(laws)

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/laws.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/laws.py.')
_out.write_text('\n'.join(_lines))
