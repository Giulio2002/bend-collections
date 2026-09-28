# Crypto contracts

Each `src/crypto` module has an executable specification in `spec/crypto/`
transcribed from its standard (HACL*'s `Spec.*` modules are the model) and a
proof package in `proofs/crypto/<module>/` whose `laws.bend` states the
public clauses and whose `proof.bend` proves them, for every input, with no
holes, axioms or `@unsafe` code (`python3 proofs/prove.py <package>` on the
pinned stock Bend). Constant time cannot be proved in Bend (there is no
timing model); where a module claims it, the claim is about the shape of
the code and is documented as such.

## ChaCha20, HChaCha20, XChaCha20

`src/crypto/chacha/core.bend` is the ChaCha core (RFC 8439 sections
2.1-2.3): the state as a sixteen-field record, one double round unrolled
(`tools/generators/chacha_gen.py`), and the block function with the number
of double rounds as a parameter (ChaCha20: 10; ChaCha8/ChaCha12 for the
random-number generators: 4/6). `src/crypto/chacha/chacha20.bend` is the
byte-level API: `chacha20_block(key, counter, nonce)`, `chacha20(key,
counter, nonce, bytes)` (RFC 8439 2.4; decryption is the same call),
`hchacha20(key, nonce16)` and `xchacha20(key, counter, nonce24, bytes)`
(draft-irtf-cfrg-xchacha-03 2.2-2.3), each `None` unless the key has 32
bytes and the nonce 12, 16 or 24; `*_rounds` and `*_unchecked` variants
take any round count / any lengths.

Specification: `spec/crypto/chacha.bend`, the RFC's pseudocode over lists:
the state is the list of sixteen words updated by position (`get`/`put`),
`quarter` is the twelve operations of 2.1 on positions a, b, c, d,
`inner_block` the eight quarter rounds of 2.3, the key and nonce are read as
little-endian words, the keystream is serialized little-endian and XORed
byte by byte, block j using counter + j (mod 2^32). HChaCha20: the ChaCha
state with the 16-byte nonce in words 12..15, twenty rounds, words 0..3 and
12..15. XChaCha20: ChaCha20 under HChaCha20(key, nonce[0..16]) with the
nonce 0x00000000 || nonce[16..24].

| Clause (`proofs/crypto/chacha/laws.bend`) | Statement | Evidence |
|---|---|---|
| `block_rounds` | `block_rounds(r, key, counter, nonce) == Spec.block_rounds(r, ...)`, every r | proved |
| `encrypt_rounds` | `encrypt_rounds(r, key, counter, nonce, pt) == Spec.encrypt_rounds(r, ...)`, every r | proved |
| `hchacha_rounds`, `hchacha20` | HChaCha20 (any r, and 10 double rounds) `== Spec.hchacha_rounds / Spec.hchacha20` | proved |
| `xencrypt` | XChaCha20 `== Spec.xencrypt` | proved |
| `chacha20_block.valid` / `.invalid` | `Some(Spec.block(...))` for a 32-byte key and 12-byte nonce, `None` otherwise | proved |
| `chacha20.valid` / `.invalid` | `Some(Spec.encrypt(...))` / `None` likewise | proved |
| `hchacha20.valid` / `.invalid` | 32-byte key, 16-byte nonce | proved |
| `xchacha20.valid` / `.invalid` | 32-byte key, 24-byte nonce | proved |
| `involution` | `encrypt_rounds(r, k, c, n, encrypt_rounds(r, k, c, n, pt)) == pt` | proved |
| `xinvolution` | the same for XChaCha20 | proved |
| `encrypt_length` | the ciphertext is as long as the plaintext | proved |
| `block_length`, `hchacha_length` | 64 and 32 bytes | proved |

All clauses hold for every key, nonce, counter and byte list (any lists of
any U32, of any length; key and nonce words read the low 8 bits of four
list elements, missing ones as absent, exactly as the specification). The
refinement follows HACL*'s `Hacl.Impl.Chacha20` against `Spec.Chacha20`:
one double round of the unrolled core is shown equal to `inner_block` on a
destructured state (`proofs/crypto/chacha/core.bend`, both sides normalize
to the same sixteen words), the round count by induction, then the
byte-level functions (`stream.bend`, `xchacha.bend`). The involution
(`involution.bend`) shows the block-by-block encryption equal to one XOR
with the concatenated keystream, which is long enough, and XOR twice
cancels (U32 XOR is proved self-inverse on Base's words).

A proof-engineering note: Bend's checker compares types by evaluating
them, so a statement mentioning twenty rounds on a symbolic key would make
it unroll them (exponential terms). The block and HChaCha20 functions are
therefore entered through a match on the key's first cell whose two arms
are the same computation (`block_rounds`/`block_body`); with a symbolic key
the call stays unevaluated, and every clause is proved for an arbitrary
round count first and instantiated.

Not proved: constant time. No branch or memory access depends on key,
nonce, counter or data bytes (only the public lengths steer the loops and
the key match looks at the list's shape, not its contents).

Tests: `tests/crypto/chacha/main.bend` (`tools/generators/chacha_tests.py`:
RFC 8439 2.3.2, 2.4.2, A.1 #1-#5, A.2 #1-#3, the XChaCha draft's HChaCha20
2.2.1 and XChaCha20 A.3.2 vectors, lengths 0-200 around the 64-byte block,
counter wrap-around, rejected key/nonce lengths, decrypt(encrypt(x)) == x;
41 vectors); `tools/check_chacha.py` (random records against `cryptography`
and a Python HChaCha20, see below).

## Poly1305

(see the Poly1305 section below)

## ChaCha20-Poly1305 and XChaCha20-Poly1305 (`src/crypto/aead.bend`)

`src/crypto/aead.bend` is the AEAD facade: `encrypt(alg, key, nonce, aad,
pt)` returns `Some(ciphertext || tag)`, `decrypt(alg, key, nonce, aad,
ciphertext || tag)` returns `Some(pt)`, for `alg` one of
`CHACHA20_POLY1305` (RFC 8439 2.8: 32-byte key, 12-byte nonce) and
`XCHACHA20_POLY1305` (draft-irtf-cfrg-xchacha-03: 24-byte nonce). Both
return `None` for other key or nonce lengths; `decrypt` returns `None` for
an input shorter than the 16-byte tag and whenever the tag is not the one
computed over aad and ciphertext, compared with `subtle.eq` before any
plaintext is produced. An algorithm is a constructor of `Alg` with its
`key_size`/`nonce_size` row and its cases in `seal`, `open` and
`expected_tag`; the facade clauses below are proved by one case per
constructor (AES-GCM adds its cases the same way).
`src/crypto/aead/chacha20poly1305.bend` has the per-algorithm functions.

Specification: `spec/crypto/chacha20poly1305.bend`, RFC 8439 2.6 and 2.8
over the ChaCha20 and Poly1305 specifications: the one-time key is the
first 32 bytes of the block with counter 0; the ciphertext is ChaCha20 from
counter 1; mac_data = aad | pad16(aad) | ciphertext | pad16(ciphertext) |
le64(len aad) | le64(len ciphertext); opening splits off the last 16 bytes
and releases the plaintext only when they equal the recomputed tag.

| Clause (`proofs/crypto/aead/laws.bend`) | Statement | Evidence |
|---|---|---|
| `chacha20poly1305.seal` / `.open` | `seal(CHACHA20_POLY1305, ...) == Spec.seal(...)`, `open(...) == Spec.open(...)` | proved |
| `xchacha20poly1305.seal` / `.open` | the same for XChaCha20-Poly1305 | proved |
| `*.encrypt`, `*.decrypt` | the per-algorithm functions are the facade's | proved |
| `encrypt.valid` / `.invalid` | `Some(seal(alg, ...))` on the algorithm's lengths, `None` otherwise | proved |
| `decrypt.valid` / `.invalid` | `open(alg, ...)` on the algorithm's lengths, `None` otherwise | proved |
| `roundtrip` | `decrypt(alg, k, n, aad, seal(alg, k, n, aad, pt)) == Some(pt)` | proved |
| `forgery` | `length(t) == 16` and `t != expected_tag(alg, k, n, aad, ct)` imply `decrypt(alg, k, n, aad, ct ++ t) == None` | proved |
| `seal_layout` | `seal(alg, k, n, aad, pt) == ct ++ expected_tag(alg, k, n, aad, ct)` for some ct | proved |

(`proofs/crypto/aead/chacha20poly1305.bend` also proves the specification's
own `roundtrip` and `forgery`, for every key and nonce list.) The
composition follows HACL*'s `Spec.Chacha20Poly1305` and the EasyCrypt proof
of Almeida et al. (2020): the AEAD is its two primitives plus framing, the
primitives entering only through their proved refinements; the round trip
uses the ChaCha20 involution, the Poly1305 tag length and `subtle.eq`'s
`Eq.refl`; forgery rejection uses `Eq.sound`.

Not proved: constant time (the only branch after the tag comparison is the
public accept/reject), and nothing about security (unforgeability is a
computational property, outside functional correctness).

Tests: `tests/crypto/aead/main.bend` (`tools/generators/aead_tests.py`:
RFC 8439 2.8.2 and XChaCha A.3.1, whose printed tags the generator asserts,
lengths around 16 and 64 bytes, decryption of sealed messages, rejection of
a flipped ciphertext bit, a flipped tag bit, a changed or dropped aad, a
wrong key or nonce, inputs shorter than a tag, wrong key/nonce lengths;
66 vectors) and `tools/check_chacha.py`: 2000 random records per operation
(ChaCha20 with random counters including wrap-around, HChaCha20, XChaCha20,
both AEADs' encryption and decryption of sealed, bit-flipped, aad-modified
and truncated inputs, occasional wrong key/nonce lengths) against
`cryptography`'s `ChaCha20Poly1305` and Python ChaCha20/HChaCha20, plus the
602 Wycheproof ChaCha20-Poly1305 and XChaCha20-Poly1305 vectors with
messages and aad of at most 128 bytes (`tests/crypto/aead/wycheproof.txt`,
including the Poly1305 edge cases). Both run in `tools/validate.py` (row
`chacha`).
