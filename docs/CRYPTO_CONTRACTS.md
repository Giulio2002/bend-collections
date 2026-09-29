# Crypto contracts

Each `src/crypto` module has an executable specification in `spec/crypto/`
transcribed from its standard (HACL*'s `Spec.*` modules are the model) and a
proof package in `proofs/crypto/<module>/` whose `laws.bend` states the
public clauses and whose `proof.bend` proves them, for every input, with no
holes, axioms or `@unsafe` code (`python3 proofs/prove.py <package>` on the
pinned stock Bend). Constant time cannot be proved in Bend (there is no
timing model); where a module claims it, the claim is about the shape of
the code and is documented as such.

## AES and AES-GCM

Modules: `src/crypto/aes/aes.bend` (FIPS 197 block cipher),
`src/crypto/aes/sbox.bend` (the S-box and the GF(2^8) doublings),
`src/crypto/aes/gcm.bend` (GHASH, GCTR, GCM), `src/crypto/aesgcm.bend` (the
byte API). Specifications: `spec/crypto/aes/poly.bend` (polynomials over
GF(2) and reduction modulo `x^n + low(x)`), `spec/crypto/aes/aes.bend`
(FIPS 197), `spec/crypto/aes/gcm.bend` (SP 800-38D). Proofs:
`proofs/crypto/aes/` (entry point `proof.bend`, clauses in `laws.bend`).

### API

```python
import ./src/crypto/aes/aes.bend as AES
import ./src/crypto/aesgcm.bend as GCM

AES.expand_key(key)              # Maybe<Schedule>: a 16-, 24- or 32-byte key
AES.encrypt_block(sched, block)  # Maybe<List>: one 16-byte block
GCM.aes128_gcm_encrypt(key, nonce, aad, pt)  # Some(ciphertext || tag) or None
GCM.aes128_gcm_decrypt(key, nonce, aad, ct)  # Some(plaintext) or None
GCM.aes256_gcm_encrypt(key, nonce, aad, pt)  # the same with a 32-byte key
GCM.aes256_gcm_decrypt(key, nonce, aad, ct)
```

Bytes are `List<&2, U32>` values below 256. Nonces are 12 bytes (96-bit IV,
`J0 = IV || 0^31 || 1`), tags 16 bytes, appended to the ciphertext. A key or
nonce of another length, or a decryption input shorter than a tag, gives
`None`; so does a tag that does not match, compared with `subtle.eq`.

### The specification

- `spec/crypto/aes/aes.bend` transcribes FIPS 197: bytes as polynomials
  (3.2), multiplication modulo `m(x) = x^8 + x^4 + x^3 + x + 1` (4.2), the
  S-box defined as in 5.1.1, the multiplicative inverse (`a^254`, which is
  `a^-1` in the 255-element group GF(2^8)*, and `{00}` to itself; proved to
  be the multiplicative inverse, clauses `Inverse.unit` / `Inverse.zero`) followed by the affine
  map of equation (5.1); ShiftRows, MixColumns (5.6) as the field products
  by `{02}` and `{03}`, AddRoundKey, the Cipher of Figure 5 and the
  KeyExpansion of Figure 11 with `Rcon[j] = [x^(j-1), 0, 0, 0]`, all for any
  `Nk`, `Nr` (AES-128: 4, 10; AES-192: 6, 12; AES-256: 8, 14). No table: the
  S-box and the round constants are computed from their definitions.
- `spec/crypto/aes/gcm.bend` transcribes SP 800-38D: blocks as elements of
  GF(2^128) in GCM's bit order (bit `i` from the left is the coefficient of
  `x^i`), the product `X * Y` as the polynomial product reduced modulo
  `x^128 + x^7 + x^2 + x + 1` (6.3), GHASH (Algorithm 2), `inc_32`, GCTR
  (Algorithm 3, a last partial block using the leftmost bytes of its
  keystream block), GCM-AE (Algorithm 4) and GCM-AD (Algorithm 5, FAIL as
  `None`, the tag compared by list equality).
- Both specs share only the neutral state types (`src/crypto/aes/types.bend`,
  a column of four bytes and a state of four columns) with the
  implementation. Byte-level field operations read the low 8 bits of a U32.

### The implementation

- The S-box is the depth-16 Boyar-Peralta circuit (113 XOR/AND gates and 4
  NOTs, the gate list of BearSSL's `aes_ct`), evaluated with one bit per
  U32, on the byte's bits extracted with shifts and masks: no table, no
  branch. `{02} * x` is `xtime` with the reduction applied through the mask
  `0 - bit7`. The key schedule is expanded once into a list of round keys.
- GHASH computes `X * H` with Algorithm 1 of SP 800-38D on four big-endian
  U32 words, one bit of `X` at a time: `Z ^= V & (0 - x_i)`,
  `V = V * x` with the reduction constant `R = 0xe1 || 0^120` applied through
  `0 - bit127`. No table (the 4-bit/8-bit Shoup tables would be indexed by
  secret data), no branch on data.
- GCTR keeps the 96-bit nonce and a U32 counter; the tag is compared with
  `subtle.eq` (`src/crypto/subtle.bend`: an OR of XORs, no early exit).
- Throughput (single thread, the server, native C backend): about 2 MB/s for
  AES-128-GCM (1 MiB in 0.49 s), the S-box circuit being most of the cost.

### Clauses (`proofs/crypto/aes/laws.bend`)

| Clause | Statement | Evidence |
|---|---|---|
| `Sbox.value` | the S-box circuit equals FIPS 197's inverse-then-affine S-box, on every U32 (both read its low byte) | proved (all 256 bytes, `sbox.bend`) |
| `Inverse.unit` / `Inverse.zero` | `S.mul(x, S.inverse(x)) == {01}` for every U32 whose low byte is nonzero; `S.inverse(0) == 0` (FIPS 197 4.4 / 5.1.1) | proved (256 closed evaluations) |
| `Cipher.value` | `encrypt(Nk, Nr, key, s)` (key expansion + cipher) equals FIPS 197's `Cipher(KeyExpansion(key))`, for every `Nk`, `Nr`, key and state | proved (`cipher.bend`) |
| `Block.value` | for a key of 16, 24 or 32 bytes and any 16-byte block, `encrypt_block(expand_key(key), block)` is the spec's AES with the key's `Nk = length / 4`, `Nr = Nk + 6` (FIPS 197 Figure 4) | proved |
| `Block.aes128`, `Block.aes192`, `Block.aes256` | a 16-, 24-, 32-byte key has `Nk` 4, 6, 8 (so `Nr` 10, 12, 14) | proved |
| `Gcm.seal`, `Gcm.open` | the implementation's GCM-AE / GCM-AD equal SP 800-38D's, for every key schedule, 96-bit nonce, AAD and input | proved (`gf.bend`, `ghash*.bend`, `gcm.bend`) |
| `Aead.roundtrip` | spec: `open(K, IV, A, seal(K, IV, A, P)) == Some(P)`, for every `Nk`, `Nr`, key, IV, AAD, message | proved (`aead.bend`) |
| `Aead.forgery` | spec: for a 16-byte `T` other than the tag of `C`, `open(K, IV, A, C || T) == None` | proved (`aead.bend`) |
| `Api128.encrypt`, `Api256.encrypt` | `aesN_gcm_encrypt(key, nonce, aad, pt) == Some(aes_seal(key, nonce, aad, pt))` (the spec's GCM-AE with the key's `Nk`, `Nr`) for a key of the right length and a 12-byte nonce | proved |
| `Api128.decrypt`, `Api256.decrypt` | `aesN_gcm_decrypt(key, nonce, aad, ct) == aes_open(key, nonce, aad, ct)` (same conditions) | proved |
| `Api128.roundtrip`, `Api256.roundtrip` | decrypting what `aesN_gcm_encrypt` returned gives `Some(pt)` | proved |
| `Api128.forgery`, `Api256.forgery` | `aesN_gcm_decrypt(key, nonce, aad, C || T) == None` when `T` is not the tag of `C` | proved |
| `ApiN.bad_key`, `ApiN.bad_key_open` | a key of another length gives `None` | proved |
| `ApiN.bad_nonce`, `ApiN.bad_nonce_open` | a nonce that is not 12 bytes gives `None` | proved |

The key size stays symbolic in every proof (`Nk = length / 4`): with a
concrete size the checker would unfold the whole key expansion of a
symbolic key (its terms grow exponentially with the rounds), which is why
the byte API computes `Nk` and `Nr` from the key length rather than from a
table of the three sizes.

The central step of the GHASH proof is algebraic (`gf.bend`, for any
modulus `x^n + low(x)`): reduction is linear, multiplication by `x` is
linear and commutes with scaling, so the reduced polynomial product
`red(a * b)` equals Algorithm 1's shift-and-add `sum a_i * (b x^i mod m)`
(Vale's `Vale.AES.GF128` / HACL*'s `Spec.GF128` relate the same two forms).
The word-level steps (`Z ^= V & mask`, `V * x`, the byte/word packing) are
proved bit by bit on the 32 bits of each word (`ghash_bits.bend`, generated
by `tools/generators/aes_ghash_proofs.py`).

What is not proved: constant time (see above); that the specification's
field is a field in general (what the cipher needs is proved on all 256
bytes: the specification's inverse `a^254` satisfies `a * a^254 = {01}` for
every nonzero byte and maps `{00}` to `{00}` (`Inverse.unit`,
`Inverse.zero`, proofs/crypto/aes/inverse.bend), and the circuit equals
the specification's S-box); anything about nonce reuse
or IV lengths other than 96 bits (not supported).

### Tests

`python3 tools/check_aes.py` (hooked into `tools/validate.py`): the FIPS 197
Appendix C vectors (AES-128/192/256); 300 NIST CAVP GCM vectors
(`tests/crypto/aes/gcm_nist.txt`: the 96-bit-IV, 128-bit-tag groups of
`gcmEncryptExtIV128/256` and `gcmDecrypt128/256`, three per length group,
including the FAIL cases); 300 random blocks against `cryptography`'s AES;
about a thousand random AES-128/256-GCM encryptions, decryptions, tampered
ciphertexts, tags and AADs, and wrong key and nonce lengths against
`cryptography`'s `AESGCM`. `tests/crypto/aes/main.bend` prints the FIPS 197
vectors.
