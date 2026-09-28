# Crypto contracts

Each `src/crypto` module has an executable specification in `spec/crypto/`
transcribed from its standard (HACL*'s `Spec.*` modules are the model) and a
proof package in `proofs/crypto/<module>/` whose `laws.bend` states the
public clauses and whose `proof.bend` proves them, for every input, with no
holes, axioms or `@unsafe` code (`python3 proofs/prove.py <package>` on the
pinned stock Bend). Constant time cannot be proved in Bend (there is no
timing model); where a module claims it, the claim is about the shape of
the code and is documented as such.

## HMAC-SHA256 and HKDF-SHA256

`src/crypto/mac.bend` (HMAC, RFC 2104 / FIPS 198-1) and `src/crypto/kdf.bend`
(HKDF, RFC 5869), on the verified SHA-256 (`src/crypto/sha`).

Specifications:

- `spec/crypto/hmac.bend`: FIPS 198-1 steps 1-9 over the FIPS 180-4
  specification `spec/crypto/sha.bend`: K0 is the key when it has at most
  64 bytes, its SHA-256 digest otherwise, zero-padded to 64 bytes;
  `hmac(K, text) = H((K0 ^ opad) || H((K0 ^ ipad) || text))`.
- `spec/crypto/hkdf.bend`: RFC 5869 section 2: `extract(salt, IKM) =
  HMAC(salt, IKM)`; `T(i) = HMAC(PRK, T(i-1) | info | i)`, N = ceil(L/32)
  (as `Nat.div(L + 31, 32)`), OKM = the first L bytes of T(1) | ... | T(N);
  `expand` is `None` for L > 255 * 32.

Implementation choices the proofs cover: `mac` decides "longer than a
block" by walking at most 65 bytes of the key (`fits`), and builds the
padded, XORed key block in one pass (`mask`); `kdf` produces blocks until
L bytes are out, with no block count and a U32 counter byte.

| Clause (`proofs/crypto/<pkg>/laws.bend`) | Statement | Evidence |
|---|---|---|
| `mac` `Sign.correct` | `sign(key, msg) == Spec.hmac(key, msg)` | proved |
| `mac` `Sign.length` | `length(sign(key, msg)) == 32` | proved |
| `mac` `Verify.value` | `verify(key, msg, tag) == SubtleSpec.equal(Spec.hmac(key, msg), tag)` | proved (through `subtle` `Eq.value`) |
| `mac` `Verify.accepts` | `verify(key, msg, sign(key, msg)) == True` | proved (`subtle` `Eq.refl`) |
| `mac` `Verify.sound` | `verify(key, msg, tag) == True` implies `tag == sign(key, msg)` | proved (`subtle` `Eq.sound`) |
| `mac` `Verify.rejects` | `tag != sign(key, msg)` implies `verify(key, msg, tag) == False` | proved |
| `kdf` `Extract.correct` | `extract(salt, ikm) == Spec.extract(salt, ikm)` | proved |
| `kdf` `Expand.correct` | `expand(prk, info, L)` is `Spec.expand` (`Fail{LengthTooLarge}` where it is `None`) | proved |
| `kdf` `Expand.done` | `L <= 8160` implies `expand(prk, info, L) == Done{Spec.okm(prk, info, L)}` | proved |
| `kdf` `Expand.too_long` | `L > 8160` implies `expand(prk, info, L) == Fail{LengthTooLarge}` | proved |
| `kdf` `Expand.length` | `expand(prk, info, L) == Done{out}` implies `length(out) == L` | proved |
| `kdf` `Expand.prefix` | `a <= b` and `expand(prk, info, b) == Done{out}` imply `expand(prk, info, a) == Done{take(out, a)}` | proved |
| `kdf` `Hkdf.correct` | `hkdf(salt, ikm, info, L)` is `Spec.hkdf` (as above) | proved |
| `kdf` `Okm.length` | `length(Spec.okm(prk, info, L)) == L`, every L | proved |
| `kdf` `Okm.prefix` | `a <= b` implies `Spec.okm(prk, info, a) == take(Spec.okm(prk, info, b), a)` | proved |

All clauses hold for every key, message, tag, salt, key material and info
(any `U32` lists, not only bytes) and every length. The proof follows
HACL*'s `Hacl.HMAC`/`Hacl.HKDF` against `Spec.HMAC`/`Spec.HKDF`, and the VST
HMAC proof (Beringer, Petcher, Ye, Appel 2015) against its FIPS 198-1
functional model: SHA-256 enters only through its proved refinement
`sha256_bytes_correct` (`proofs/crypto/sha/laws.bend`), and the key block
lemma (`proofs/crypto/mac/hmac.bend`) shows the one-pass `mask` equal to
FIPS 198-1's pad-then-XOR. For HKDF (`proofs/crypto/kdf/okm.bend`), the
block stream cut to `rem` bytes equals the first `rem` bytes of
T(i+1) | ... | T(i+n) whenever `rem <= 32 n` (`go_chain`), and
`L <= 32 * ceil(L/32)` (`ceil_ok`, from Base's `Nat.divmod`).

Not proved: that `verify` runs in constant time. It compares with
`subtle.eq` (one pass over the tag, the XOR of each byte pair ORed into an
accumulator, no early exit on the contents; the lengths, which are public,
are compared directly), and nothing else in `verify` branches on the tag.
The key-length test in `sign` branches on the length of the key, which is
not secret in HMAC's model; `mask` and SHA-256 do not branch on key or
message bytes.

Tests: `tests/crypto/mac/main.bend` (RFC 4231 test cases 1-7, case 5
truncated to 128 bits as in the RFC, verify on each RFC tag, rejection of
flipped, truncated, extended, empty and other-key tags, 64- and 65-byte
keys) and `tests/crypto/kdf/main.bend` (RFC 5869 A.1-A.3 PRK and OKM, the
0, 32, 8160 and 8161 byte lengths), both self-checking; `tools/check_mac.py`
builds and runs both, re-derives their RFC constants with `hmac` and
`cryptography`, and runs a differential test (3000 records by default:
sign, verify with right and tampered tags, hkdf, expand, extract, with
lengths around the 64-byte block and the 8160-byte limit) against Python's
`hmac`/`hashlib` and the `cryptography` package's `HMAC`, `HKDF` and
`HKDFExpand`. It runs in `tools/validate.py` (row `mac`).
