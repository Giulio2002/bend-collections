# Benchmarks

Every row runs the same algorithm in Bend (native C backend, one thread) and in C
(`-O3 -march=native`), with identical inputs, and the two results must agree
(a checksum of every result, or the full digests). **Ratio = Bend time / C time**:
below 1 Bend is faster.

Machine: arm64, macOS-15.6-arm64-arm-64bit-Mach-O. Measured while other work was running on the machine, so
absolute times are noisy; each sample alternates Bend and C under the same load,
so the ratios are the meaningful column.

Toolchain: Bend 2.0.34 (the release pinned in `tools/toolchain.json`), every table
measured with it; C: Apple clang version 17.0.0 (clang-1700.6.3.2).

Reproduce:

```sh
python3 benchmarks/full_sweep.py --report build/bench/full.json   # containers
python3 benchmarks/crypto.py --report build/bench/crypto.json      # hashes
python3 benchmarks/natural.py --report build/bench/math.json       # math
python3 benchmarks/typed.py --report build/bench/typed.json        # math per type
python3 benchmarks/maps/compare.py --report build/bench/maps.json  # HashMap vs Base.Map
python3 benchmarks/intrusive.py --report build/bench/intrusive.json # intrusive list
python3 benchmarks/crypto_suite.py --group hash   --report build/bench/suite-hash.json
python3 benchmarks/crypto_suite.py --group cipher --report build/bench/suite-cipher.json
python3 benchmarks/crypto_suite.py --group pk     --report build/bench/suite-pk.json
python3 benchmarks/crypto_suite.py --group random --report build/bench/suite-random.json
python3 benchmarks/render.py                                        # this file
```

On the maintainer's Mac every command runs through `bench-local` (one run at a
time, never alongside a proof check).

## Worst ratio per module

The largest Bend / C ratio of each table below (for AES-GCM, against the
constant-time C). Hash map vs Base.Map compares two Bend structures and is not listed.

| Module | Worst ratio |
|---|---:|
| SHA-256 | 1.91 |
| Keccak-256 | 3.72 |
| BLAKE2s | 1.14 |
| BLAKE2b | 2.70 |
| BLAKE3 | 1.58 |
| SHA-512 | 9.44 |
| SHA3-256 | 11.68 |
| Incremental hashing (`Hasher`) | 37.89 |
| `subtle.eq` | 213.33 |
| HMAC-SHA256 | 5.84 |
| HKDF-SHA256 | 8.97 |
| ChaCha20 | 26.28 |
| Poly1305 | 1135.42 |
| ChaCha20-Poly1305 | 366.20 |
| XChaCha20-Poly1305 | 347.95 |
| AES-128-GCM | 31.60 |
| AES-256-GCM | 30.60 |
| X25519 shared secret | 1677.75 |
| Ed25519 key generation | 7064.08 |
| Ed25519 sign | 13116.15 |
| Ed25519 verify | 4449.20 |
| Argon2id | 42.94 |
| secp256k1 (ECDSA, recovery, BIP-340) | 47560.98 |
| ChaCha8 `uint64` | 7.26 |
| PCG `uint64` | 6.47 |
| `uint_below` (ChaCha8) | 6.05 |
| `float64` (ChaCha8) | 9.28 |
| `shuffle` (ChaCha8) | 6.38 |
| `crypto.random.bytes` | 23.17 |
| `crypto.random.read_words` | 4.34 |
| Math (natural) | 5.35 |
| Math per type | 7.68 |
| Intrusive doubly linked list | 1.63 |
| Dynamic array | 13.49 |
| Deque | 1.15 |
| FIFO queue | 1.44 |
| Stack | 19.67 |
| Simple queue | 1.40 |
| Priority queue | 5.54 |
| Binary heap | 5.56 |
| Doubly linked list | 12.40 |
| List iterator | 3.86 |
| Tree map | 26.52 |
| Bitset | 3.32 |
| Bit list | 5.66 |
| Hash map | 21.75 |
| LRU cache | 10.74 |

## Hashes

Median of five alternating samples per size, after a warm-up; inputs prepared
before the timed region. Microseconds per hash.

### SHA-256

C reference: portable FIPS 180-4 C (`benchmarks/native/sha256.c`). Worst ratio 1.91.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 0.38 | 0.29 | 1.30 |
| 1 KiB | 4.39 | 2.46 | 1.79 |
| 16 KiB | 70.3 | 37.0 | 1.90 |
| 64 KiB | 281 | 147 | 1.91 |
| 1 MiB | 4500 | 2358 | 1.91 |

### Keccak-256

C reference: XKCP `plain-64bits` fully unrolled (`benchmarks/native/xkcp/`). Worst ratio 3.72.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.50 | 0.13 | 3.72 |
| 64 B | 0.50 | 0.14 | 3.70 |
| 1 KiB | 3.78 | 1.08 | 3.52 |
| 16 KiB | 57.6 | 16.2 | 3.55 |
| 64 KiB | 230 | 64.9 | 3.55 |
| 1 MiB | 3688 | 1054 | 3.50 |

### BLAKE2s

C reference: official BLAKE2 reference `blake2s-ref.c`. Worst ratio 1.14.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.08 | 0.07 | 1.06 |
| 64 B | 0.08 | 0.07 | 1.14 |
| 1 KiB | 1.10 | 1.10 | 1.00 |
| 16 KiB | 18.6 | 18.3 | 1.01 |
| 64 KiB | 82.0 | 78.2 | 1.05 |
| 1 MiB | 1188 | 1149 | 1.03 |

### BLAKE2b

C reference: official BLAKE2 reference `blake2b-ref.c`. Worst ratio 2.70.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.24 | 0.09 | 2.70 |
| 64 B | 0.24 | 0.09 | 2.57 |
| 1 KiB | 1.71 | 0.68 | 2.53 |
| 16 KiB | 26.4 | 10.6 | 2.49 |
| 64 KiB | 105 | 42.2 | 2.50 |
| 1 MiB | 1750 | 680 | 2.57 |

### BLAKE3

C reference: official BLAKE3 C, portable only (no SIMD). Worst ratio 1.58.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.09 | 0.06 | 1.58 |
| 64 B | 0.08 | 0.06 | 1.36 |
| 1 KiB | 0.85 | 0.78 | 1.10 |
| 16 KiB | 13.7 | 13.0 | 1.06 |
| 64 KiB | 54.7 | 51.9 | 1.05 |
| 1 MiB | 938 | 838 | 1.12 |

## More hashes

Same method as the hashes above (`benchmarks/crypto_suite.py --group hash`).

### SHA-512

C reference: Monocypher 4.0.2 `crypto_sha512` (portable C). Worst ratio 9.44.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 1.98 | 0.23 | 8.70 |
| 1 KiB | 14.2 | 1.50 | 9.44 |
| 16 KiB | 184 | 20.6 | 8.91 |
| 64 KiB | 734 | 81.8 | 8.98 |
| 1 MiB | 12250 | 1306 | 9.38 |

### SHA3-256

C reference: XKCP `plain-64bits` Keccak-p[1600] with the FIPS 202 padding. Worst ratio 11.68.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 1.59 | 0.14 | 11.68 |
| 1 KiB | 11.0 | 1.08 | 10.19 |
| 16 KiB | 152 | 16.3 | 9.36 |
| 64 KiB | 594 | 64.9 | 9.15 |
| 1 MiB | 10000 | 1041 | 9.60 |

### Incremental hashing (`Hasher`)

C reference: the same C as the one-shot rows through init/update/final (`sha256_ctx.h`, Monocypher `crypto_sha512_*`, `sha3_ctx.h` over XKCP), fed the same chunks. "one-shot" is `hash.sha256`/`sha512`/`sha3_256` of the whole message; "64 B chunks" is `new_*`, `update_all` over 64-byte pieces cut before the timed region, then `digest`. Worst ratio 37.89.

| Hash, message, feed | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| SHA-256 1 KiB one-shot | 8.30 | 2.52 | 3.30 |
| SHA-256 1 KiB 64 B chunks | 26.9 | 2.58 | 10.41 |
| SHA-256 64 KiB one-shot | 531 | 148 | 3.59 |
| SHA-256 64 KiB 64 B chunks | 1625 | 149 | 10.87 |
| SHA-256 1 MiB one-shot | 8500 | 2368 | 3.59 |
| SHA-256 1 MiB 64 B chunks | 26500 | 2382 | 11.13 |
| SHA-512 1 KiB one-shot | 23.9 | 1.50 | 15.96 |
| SHA-512 1 KiB 64 B chunks | 43.0 | 1.50 | 28.59 |
| SHA-512 64 KiB one-shot | 1281 | 82.0 | 15.62 |
| SHA-512 64 KiB 64 B chunks | 2469 | 81.8 | 30.20 |
| SHA-512 1 MiB one-shot | 21000 | 1308 | 16.06 |
| SHA-512 1 MiB 64 B chunks | 40500 | 1302 | 31.11 |
| SHA3-256 1 KiB one-shot | 19.0 | 1.08 | 17.61 |
| SHA3-256 1 KiB 64 B chunks | 45.9 | 1.30 | 35.27 |
| SHA3-256 64 KiB one-shot | 1125 | 65.0 | 17.30 |
| SHA3-256 64 KiB 64 B chunks | 2969 | 78.3 | 37.89 |
| SHA3-256 1 MiB one-shot | 18500 | 1040 | 17.78 |
| SHA3-256 1 MiB 64 B chunks | 47000 | 1264 | 37.20 |

### `subtle.eq`

C reference: constant-time loop (lengths, then OR of the XOR of every byte pair, no early exit); equal inputs, so every byte is compared. Worst ratio 213.33.

| Length | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 32 B | 0.14 | 0.00 | 128.38 |
| 1 KiB | 3.91 | 0.02 | 213.33 |
| 64 KiB | 219 | 1.16 | 189.19 |

### HMAC-SHA256

C reference: RFC 2104 over the portable FIPS 180-4 SHA-256 (`benchmarks/native/sha256_ctx.h`), 32-byte key. Worst ratio 5.84.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 4.43 | 0.76 | 5.84 |
| 1 KiB | 13.2 | 2.98 | 4.43 |
| 16 KiB | 141 | 37.7 | 3.73 |
| 64 KiB | 531 | 149 | 3.56 |
| 1 MiB | 8500 | 2371 | 3.58 |

### HKDF-SHA256

C reference: RFC 5869 over the same C HMAC; 32-byte input keying material, 32-byte salt, 16-byte info. Worst ratio 8.97.

| Output | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 32 B out | 9.28 | 1.24 | 7.51 |
| 128 B out | 25.9 | 3.12 | 8.29 |
| 1024 B out | 180 | 20.5 | 8.78 |
| 8160 B out | 1406 | 157 | 8.97 |

## Ciphers and AEADs

### ChaCha20

C reference: Monocypher 4.0.2 `crypto_chacha20_ietf` (portable C). Worst ratio 26.28.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 2.32 | 0.09 | 26.28 |
| 1 KiB | 24.9 | 1.08 | 23.01 |
| 16 KiB | 414 | 17.0 | 24.31 |
| 64 KiB | 1688 | 67.9 | 24.85 |
| 1 MiB | 27500 | 1090 | 25.23 |

### Poly1305

C reference: Monocypher 4.0.2 `crypto_poly1305` (portable C). Worst ratio 1135.42.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 28.4 | 0.04 | 701.81 |
| 1 KiB | 416 | 0.39 | 1054.46 |
| 16 KiB | 6688 | 6.02 | 1111.69 |
| 64 KiB | 27250 | 24.0 | 1135.42 |
| 1 MiB | 426000 | 381 | 1118.11 |

### ChaCha20-Poly1305

C reference: Monocypher 4.0.2 `crypto_aead_init_ietf` + `crypto_aead_write`/`_read`. Worst ratio 366.20.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 41.4 | 0.24 | 170.69 |
| 1 KiB | 584 | 1.59 | 366.20 |
| 16 KiB | 8094 | 23.8 | 340.57 |
| 64 KiB | 30562 | 93.3 | 327.53 |
| 1 MiB | 490000 | 1502 | 326.23 |
| 1 KiB open | 510 | 1.60 | 319.07 |
| 64 KiB open | 32125 | 92.9 | 345.90 |

### XChaCha20-Poly1305

C reference: Monocypher 4.0.2 `crypto_aead_lock`/`_unlock`. Worst ratio 347.95.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 42.1 | 0.32 | 132.76 |
| 1 KiB | 589 | 1.69 | 347.95 |
| 16 KiB | 7750 | 23.6 | 328.26 |
| 64 KiB | 30688 | 93.4 | 328.43 |
| 1 MiB | 491000 | 1493 | 328.87 |
| 1 KiB open | 512 | 1.65 | 309.33 |
| 64 KiB open | 32125 | 95.8 | 335.51 |

### AES-128-GCM

C reference: BearSSL `br_gcm` with the constant-time bitsliced `br_aes_ct64` and `br_ghash_ctmul64` (the "C ct" column); the "C table" column swaps in the table-based `br_aes_big` (not constant-time). Worst ratio 31.60.

| Message | Bend (us) | C ct (us) | Ratio | C table (us) | Ratio vs table |
|---:|---:|---:|---:|---:|---:|
| 64 B | 18.3 | 1.21 | 15.14 | 0.36 | 50.81 |
| 1 KiB | 156 | 5.82 | 26.86 | 3.14 | 49.81 |
| 16 KiB | 2312 | 79.5 | 29.09 | 47.6 | 48.56 |
| 64 KiB | 9500 | 316 | 30.02 | 190 | 49.93 |
| 1 MiB | 152000 | 5047 | 30.12 | 3014 | 50.43 |
| 1 KiB open | 172 | 5.85 | 29.37 | 3.11 | 55.28 |
| 64 KiB open | 10000 | 316 | 31.60 | 188 | 53.19 |

### AES-256-GCM

C reference: as AES-128-GCM, with a 32-byte key. Worst ratio 30.60.

| Message | Bend (us) | C ct (us) | Ratio | C table (us) | Ratio vs table |
|---:|---:|---:|---:|---:|---:|
| 64 B | 23.9 | 1.58 | 15.10 | 0.45 | 52.72 |
| 1 KiB | 191 | 7.57 | 25.28 | 4.03 | 47.48 |
| 16 KiB | 2875 | 104 | 27.74 | 61.4 | 46.80 |
| 64 KiB | 11250 | 411 | 27.39 | 245 | 45.92 |
| 1 MiB | 184000 | 6527 | 28.19 | 3900 | 47.18 |
| 1 KiB open | 203 | 7.55 | 26.89 | 4.04 | 50.29 |
| 64 KiB open | 12500 | 408 | 30.60 | 242 | 51.65 |

## Public-key and password hashing

A curve operation takes Bend 0.1-1 s, so these rows time a few operations
per sample (Argon2id: 64 hashes at 64 KiB, one at 19 MiB). The curve C
references repeat their timed pass until 50 ms have passed and report the
mean pass. Microseconds per operation.

### X25519 shared secret

C reference: Monocypher 4.0.2 `crypto_x25519`. Worst ratio 1677.75.

| Operation | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| shared secret | 53625 | 32.0 | 1677.75 |

### Ed25519 key generation

C reference: Monocypher 4.0.2 `crypto_ed25519_key_pair` (SHA-512). Worst ratio 7064.08.

| Operation | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| keygen | 118500 | 16.8 | 7064.08 |

### Ed25519 sign

C reference: Monocypher 4.0.2 `crypto_ed25519_sign`. Worst ratio 13116.15.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| sign 64 B | 231500 | 17.6 | 13116.15 |
| sign 1 KiB | 232000 | 20.1 | 11542.29 |

### Ed25519 verify

C reference: Monocypher 4.0.2 `crypto_ed25519_check`. Worst ratio 4449.20.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| verify 64 B | 208000 | 46.8 | 4449.20 |
| verify 1 KiB | 210500 | 47.8 | 4403.77 |

### Argon2id

C reference: the official P-H-C reference (`ref.c`, portable, no SSE), one thread. Worst ratio 42.94.

| Parameters | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| m=64 KiB t=3 p=1 | 2547 | 59.3 | 42.94 |
| m=19 MiB t=2 p=1 | 462000 | 12954 | 35.66 |

### secp256k1 (ECDSA, recovery, BIP-340)

C reference: libsecp256k1 v0.6.0 (precomputed tables, 5x52 field, no assembly; recovery, extrakeys and schnorrsig modules); the Bend side is `src/crypto/secp256k1.bend` (#26). Worst ratio 47560.98.

| Operation | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| ECDSA sign | 105500 | 11.8 | 8978.72 |
| ECDSA verify | 202000 | 14.3 | 14076.66 |
| ECDSA recover | 203000 | 15.1 | 13443.71 |
| BIP-340 sign | 390000 | 8.20 | 47560.98 |
| BIP-340 verify | 196000 | 14.4 | 13611.11 |

## Random

Fixed seeds (ChaCha8: bytes `7i + 1`; PCG: `NewPCG(1, 2)`); every draw is stored
and folded into the checksum after the timed region. Nanoseconds per draw, or
microseconds per shuffle / per request.

### ChaCha8 `uint64`

C reference: a C transcription of Go 1.23 `internal/chacha8rand` (portable block function). Worst ratio 7.26.

| Draws | Bend (ns) | C (ns) | Ratio |
|---:|---:|---:|---:|
| 2097152 draws | 32.9 | 4.53 | 7.26 |

### PCG `uint64`

C reference: a C transcription of Go 1.23 `math/rand/v2` PCG-DXSM. Worst ratio 6.47.

| Draws | Bend (ns) | C (ns) | Ratio |
|---:|---:|---:|---:|
| 4194304 draws | 11.2 | 1.73 | 6.47 |

### `uint_below` (ChaCha8)

C reference: Go's `uint64n` (Lemire) transcribed. Worst ratio 6.05.

| Bound | Bend (ns) | C (ns) | Ratio |
|---:|---:|---:|---:|
| n = 1000000007 | 35.8 | 5.91 | 6.05 |
| n = 2^63 + 1 | 98.2 | 17.2 | 5.71 |

### `float64` (ChaCha8)

C reference: Go's `Float64` transcribed. Worst ratio 9.28.

| Draws | Bend (ns) | C (ns) | Ratio |
|---:|---:|---:|---:|
| 2097152 draws | 41.5 | 4.47 | 9.28 |

### `shuffle` (ChaCha8)

C reference: Go's Fisher-Yates `Shuffle` on a C array; Bend's `shuffle_array` on an `Array<U32>`, in place. Worst ratio 6.38.

| Items | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 1000 items | 27.5 | 4.44 | 6.19 |
| 10000 items | 270 | 43.3 | 6.23 |
| 100000 items | 3150 | 494 | 6.38 |

### `crypto.random.bytes`

C reference: Go's `ChaCha8.Read` transcribed; Bend returns a list of bytes. Worst ratio 23.17.

| Request | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 0.79 | 0.04 | 22.37 |
| 1 KiB | 12.2 | 0.57 | 21.52 |
| 64 KiB | 797 | 35.6 | 22.36 |
| 1 MiB | 13250 | 572 | 23.17 |

### `crypto.random.read_words`

C reference: Go's `ChaCha8.Read` transcribed; Bend writes the bytes packed into an `Array<U32>`, in place. Worst ratio 4.34.

| Request | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 0.15 | 0.04 | 4.29 |
| 1 KiB | 2.44 | 0.59 | 4.17 |
| 64 KiB | 156 | 36.0 | 4.34 |
| 1 MiB | 2500 | 578 | 4.33 |

## C references

Every reference is portable C compiled with `-O3 -march=native -std=c11`: no
assembly, no intrinsics, no AES/SHA/PMULL instructions (the compiler may still
auto-vectorize). Vendored sources are unmodified; each directory has its licence
and a REVISION file.

| Reference | Version | Licence | Used for | Timing behaviour |
|---|---|---|---|---|
| `benchmarks/native/sha256.c`, `sha256_ctx.h` | written for this repo (FIPS 180-4, RFC 2104, RFC 5869) | MIT (this repo) | SHA-256, incremental SHA-256, HMAC-SHA256, HKDF-SHA256 | constant-time (no secret-indexed tables) |
| XKCP `plain-64bits` (`benchmarks/native/xkcp/`) | commit eb5244d6 | CC0 | Keccak-256, SHA3-256 (+ `sha3_ctx.h` sponge) | constant-time |
| BLAKE2 reference (`benchmarks/native/blake/`) | commit ed1974ea | CC0 / Apache-2.0 | BLAKE2s, BLAKE2b | constant-time |
| BLAKE3 C, portable only (`benchmarks/native/blake/`) | commit 6aab490a | CC0 / Apache-2.0 | BLAKE3 | constant-time |
| Monocypher (`benchmarks/native/monocypher/`) | 4.0.2 (commit 0d85f98c) | BSD-2-Clause / CC0 | SHA-512, ChaCha20, Poly1305, (X)ChaCha20-Poly1305, X25519, Ed25519 | constant-time |
| BearSSL (`benchmarks/native/bearssl/`) | commit 7bea48e5 (2026-04-06) | MIT | AES-GCM: `aes_ct64` + `ghash_ctmul64` (C ct), `aes_big` (C table) | ct64/ctmul64 constant-time (bitsliced, 4 blocks at a time); `aes_big` table lookups, **not** constant-time |
| Argon2 reference (`benchmarks/native/argon2/`) | P-H-C phc-winner-argon2 commit f57e61e1 (2021-06-25) | CC0 / Apache-2.0 | Argon2id | `ref.c`, portable; data-independent addressing in the first half-pass as the RFC specifies |
| libsecp256k1 (`benchmarks/native/secp256k1/`) | v0.6.0 (commit 0cdc758a) | MIT | secp256k1 | constant-time signing |
| `benchmarks/native/gorand.h` | transcription of Go 1.23 `internal/chacha8rand` and `math/rand/v2` (pcg.go, rand.go, chacha8.go) | BSD-3-Clause (Go) | ChaCha8, PCG, `uint_below`, `float64`, shuffle, `crypto.random.bytes` | portable block function (Go itself uses SIMD) |
| `suite_subtle_eq.c` | written for this repo | MIT (this repo) | `subtle.eq` | constant-time loop |

Fairness notes:

- Bend runs single-threaded (`--threads 1`) on byte lists (one U32 per byte);
  C works on byte arrays in place. Input parsing and message cutting happen
  before the timed region on both sides; the checksum after it.
- The Bend AES is constant-time (the Boyar-Peralta S-box circuit on one byte at
  a time, GHASH bit by bit). The fair column is BearSSL `aes_ct64`; the table
  column shows what a non-constant-time C costs.
- AES-GCM and the AEADs set up the key for every message on both sides (the
  Bend API takes the key bytes per call).
- Ed25519 sign: the Bend API takes the 32-byte seed and derives the public key
  inside every call; Monocypher's `crypto_ed25519_sign` takes the 64-byte
  expanded secret key (seed || public key), so it skips one fixed-base
  scalar multiplication per signature.
- secp256k1: libsecp256k1 is production code with precomputed multiplication
  tables, not a plain reference; its verify parses the key and signature inside
  the timed region (the Bend API takes bytes) and normalises s (Bend's verify
  accepts high s). Bend's BIP-340 sign derives the public key on every call.
  No Python check (Bend and C must agree; RFC 6979 and fixed BIP-340 aux make
  both deterministic).
- Shuffle: both sides shuffle the first n slots of an array in place (Bend:
  `shuffle_array` on an `Array<U32>` of 2^d >= n slots, filled before the timed
  region; the list `shuffle` writes the list into such an array and reads it
  back, two more linear passes).
- `crypto.random.bytes` returns a list with one heap cell per byte (and
  reverses its accumulator), so it stays about 20x the C buffer write; the
  ChaCha8 stream alone is about 7x. `crypto.random.read_words` writes the same
  bytes packed four to a U32 into an `Array<U32>` allocated before the timed
  region, which is what the C side does with its byte buffer.

## Math

`src/math/natural.bend` against idiomatic C (`benchmarks/native/math.c`: Euclid
with `%`, `sqrt` plus an integer correction, `__builtin_clzll`, binary
exponentiation, extended Euclid). Each row makes COUNT calls on arguments from
the same MINSTD stream and folds every result into a checksum that must agree;
the `loop` row is the generator and the fold alone, and is part of every other
row. Median of five alternating samples after a warm-up; nanoseconds per call.

| Operation | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|
| loop | 5.35 | 5.44 | 0.98 |
| gcd | 56.2 | 56.1 | 1.00 |
| lcm | 37.8 | 38.5 | 0.98 |
| isqrt | 19.9 | 5.43 | 3.66 |
| iroot3 | 52.2 | 9.76 | 5.35 |
| ilog10 | 5.40 | 10.2 | 0.53 |
| bit_length | 12.7 | 5.36 | 2.37 |
| factorial | 12.3 | 11.3 | 1.09 |
| perm | 13.7 | 11.9 | 1.16 |
| comb | 12.6 | 12.2 | 1.04 |
| pow_mod | 53.5 | 53.2 | 1.01 |
| mod_inverse | 63.7 | 45.6 | 1.40 |
| divmod | 6.12 | 5.44 | 1.13 |

### Math per type

The templated math of `src/math/generic.bend` instantiated for U32, U64 (two
U32 words) and F32, and the software binary64 of `src/math/f64.bend`, against
C with `uint32_t`, `uint64_t` (a 128-bit product for `mod m`), `float` and
`double` (`benchmarks/native/typed.c`), with the same checked semantics (a
result that does not fit counts as 0) and the same square-and-multiply order
for powers. The F64 rows compare software arithmetic with the hardware FPU;
the rounding, conversion, exponent, neighbour and remainder rows (`f64_floor`
to `f64_nextafter`) compare with libm's `floor`, `nearbyint`, `fmod`,
`remainder`, `frexp`, `ldexp` and `nextafter` and a `(uint64_t)` cast.
Same method as above; nanoseconds per call.

| Operation | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|
| loop | 5.75 | 5.91 | 0.97 |
| u32_gcd | 95.5 | 61.1 | 1.56 |
| u32_isqrt | 6.30 | 6.54 | 0.96 |
| u32_comb | 35.2 | 27.7 | 1.27 |
| u32_factorial | 11.2 | 10.9 | 1.03 |
| u32_pow_mod | 312 | 98.8 | 3.15 |
| u64_gcd | 195 | 113 | 1.72 |
| u64_isqrt | 24.2 | 6.52 | 3.72 |
| u64_comb | 133 | 43.3 | 3.08 |
| u64_factorial | 19.3 | 12.3 | 1.58 |
| u64_pow_mod | 586 | 489 | 1.20 |
| f32_pow | 9.40 | 8.62 | 1.09 |
| f32_clamp | 6.10 | 5.98 | 1.02 |
| f64_add | 7.33 | 5.84 | 1.26 |
| f64_mul | 14.0 | 5.93 | 2.36 |
| f64_div | 40.0 | 5.87 | 6.81 |
| f64_sqrt | 44.0 | 5.73 | 7.68 |
| f64_pow | 56.0 | 8.57 | 6.53 |
| u32_checked_mul | 6.00 | 5.90 | 1.02 |
| u64_checked_mul | 7.50 | 5.91 | 1.27 |
| u32_bit_count | 16.5 | 5.88 | 2.81 |
| u64_bit_count | 26.5 | 5.88 | 4.50 |
| u32_is_prime | 77.5 | 50.9 | 1.52 |
| u32_next_prime | 900 | 590 | 1.53 |
| egcd | 100 | 82.0 | 1.22 |
| f64_floor | 11.8 | 5.90 | 1.99 |
| f64_round | 11.8 | 5.90 | 1.99 |
| f64_to_u64 | 6.00 | 5.83 | 1.03 |
| f64_fmod | 123 | 61.0 | 2.02 |
| f64_remainder | 127 | 200 | 0.63 |
| f64_frexp | 7.08 | 6.11 | 1.16 |
| f64_ldexp | 10.0 | 6.01 | 1.66 |
| f64_nextafter | 5.67 | 6.15 | 0.92 |

### Intrusive doubly linked list

Entity workloads from `benchmarks/intrusive.py` (contributed in
[#5](https://github.com/Giulio2002/bend-collections/pull/5)): **transfer** removes an
entity from one list and prepends it to another; **pulses** is a pooled
lifecycle. The same application-owned entity array drives the intrusive list
(links inside the entities), the handle-checked `DList`, and C. Every run
must produce the reference checksum; the hot loops allocate nothing (checked
with positive controls). Median of the samples, nanoseconds per unit.

| Workload | Entities | Intrusive (ns) | DList (ns) | C (ns) | Intrusive / C | DList / Intrusive |
|---|---:|---:|---:|---:|---:|---:|
| transfer | 32 | 2.88 | 31.35 | 2.01 | 1.43 | 10.9 |
| transfer | 1024 | 2.48 | 31.60 | 1.52 | 1.63 | 12.7 |
| transfer | 65536 | 2.88 | 35.88 | 2.17 | 1.33 | 12.4 |
| pulses | 32 | 2.60 | 5.68 | 2.76 | 0.94 | 2.2 |
| pulses | 1024 | 3.01 | 5.25 | 2.95 | 1.02 | 1.7 |
| pulses | 65536 | 2.69 | 5.84 | 2.89 | 0.93 | 2.2 |

## Containers

Each row measures one public operation at three structure sizes. The time of
an operation is the difference between two regions that run 2k and k of them
(build, settle and teardown cancel); removals are measured in a restoring pair
with the insertion that puts the element back. Nanoseconds per operation,
median of six samples. A sample in which other load interrupted a region (A - B
negative or under the timing minimum) is re-taken, both sides together, up to
four times; failed rows are re-measured with `full_sweep.py --retry-failed`.
See `benchmarks/run.py` for the method.

† quick sampling (`BENCH_QUICK=1`): a 20 ms instead of 50 ms minimum difference and
three samples instead of six, several rows in parallel. Expect about ±10% on
those ratios; the unmarked rows use the full method.

### Dynamic array

Worst ratio 13.49.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 8.24 | 2.94 | 2.80 |
| push | medium | 8.20 | 2.92 | 2.81 |
| push | large | 10.9 | 3.66 | 2.97 |
| get | small | 10.9 | 1.28 | 8.51 |
| get | medium | 10.7 | 1.16 | 9.23 |
| get | large | 16.1 | 1.20 | 13.49 |
| set | small | 1.70 | 1.27 | 1.34 |
| set | medium | 1.61 | 1.14 | 1.41 |
| set | large | 1.94 | 1.14 | 1.71 |
| length | small | 0.93 | 2.62 | 0.35 |
| length | medium | 0.91 | 2.62 | 0.35 |
| length | large | 0.92 | 2.64 | 0.35 |
| capacity | small | 0.92 | 2.28 | 0.40 |
| capacity | medium | 0.92 | 2.28 | 0.40 |
| capacity | large | 0.94 | 2.35 | 0.40 |
| reserve | small | 1.16 | 1.09 | 1.07 |
| reserve | medium | 1.17 | 1.09 | 1.07 |
| reserve | large | 1.18 | 1.09 | 1.08 |
| to_list | small | 182 | 75.0 | 2.42 |
| to_list | medium | 9192 | 4185 | 2.20 |
| to_list | large | 494000 | 315940 | 1.56 |
| clear | small | 0.99 | 1.49 | 0.66 |
| clear | medium | 1.00 | 1.50 | 0.67 |
| clear | large | 1.02 | 1.55 | 0.66 |
| pop | small | 4.07 | 2.45 | 1.66 |
| pop | medium | 4.02 | 2.42 | 1.66 |
| pop | large | 3.97 | 2.48 | 1.60 |
| new | small | 5.47 | 2.42 | 2.26 |
| new | medium | 5.64 | 2.38 | 2.37 |
| new | large | 7.75 | 2.39 | 3.24 |

### Deque

Worst ratio 1.15.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | 11.3 | 10.5 | 1.08 |
| push_front | medium | 11.3 | 10.5 | 1.08 |
| push_front | large | 11.6 | 10.6 | 1.09 |
| push_back | small | 11.2 | 10.5 | 1.07 |
| push_back | medium | 11.3 | 10.3 | 1.10 |
| push_back | large | 10.5 | 13.9 | 0.76 |
| peek_front | small | 3.79 | 3.43 | 1.10 |
| peek_front | medium | 3.78 | 3.47 | 1.09 |
| peek_front | large | 3.88 | 3.51 | 1.10 |
| peek_back | small | 3.75 | 3.43 | 1.09 |
| peek_back | medium | 3.77 | 3.41 | 1.10 |
| peek_back | large | 3.76 | 3.34 | 1.13 |
| length | small | 0.95 | 2.33 | 0.41 |
| length | medium | 0.92 | 2.33 | 0.40 |
| length | large | 1.04 | 2.58 | 0.40 |
| to_list | small | 709 | 654 | 1.08 |
| to_list | medium | 49625 | 43179 | 1.15 |
| to_list | large | 3110000 | 3071800 | 1.01 |
| pop_front | small | 5.16 | 9.90 | 0.52 |
| pop_front | medium | 5.00 | 9.01 | 0.56 |
| pop_front | large | 7.48 | 8.84 | 0.85 |
| pop_back | small | 4.96 | 9.02 | 0.55 |
| pop_back | medium | 4.96 | 8.97 | 0.55 |
| pop_back | large | 7.44 | 8.84 | 0.84 |
| new | small | 0.96 | 1.23 | 0.79 |
| new | medium | 0.96 | 1.22 | 0.78 |
| new | large | 0.95 | 1.23 | 0.77 |

### FIFO queue

Worst ratio 1.44.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| enqueue | small | 7.94 | 10.4 | 0.76 |
| enqueue | medium | 8.10 | 10.4 | 0.78 |
| enqueue | large | 8.00 | 10.3 | 0.78 |
| peek | small | 3.59 | 3.38 | 1.06 |
| peek | medium | 3.39 | 3.38 | 1.00 |
| peek | large | 3.27 | 3.32 | 0.99 |
| length | small | 0.95 | 2.63 | 0.36 |
| length | medium | 0.94 | 2.67 | 0.35 |
| length | large | 0.92 | 2.63 | 0.35 |
| to_list | small | 675 | 670 | 1.01 |
| to_list | medium | 49667 | 45590 | 1.09 |
| to_list | large | 3170000 | 2957970 | 1.07 |
| dequeue | small | 13.3 | 9.23 | 1.44 |
| dequeue | medium | 9.53 | 9.57 | 1.00 |
| dequeue | large | 12.1 | 11.1 | 1.08 |
| new | small | 0.95 | 1.23 | 0.77 |
| new | medium | 0.94 | 1.23 | 0.76 |
| new | large | 0.95 | 1.22 | 0.78 |

### Stack

Worst ratio 19.67.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 8.27 | 15.7 | 0.53 |
| push | medium | 8.24 | 13.8 | 0.60 |
| push | large | 8.55 | 15.9 | 0.54 |
| peek | small | 1.48 | 1.00 | 1.48 |
| peek | medium | 1.48 | 1.01 | 1.47 |
| peek | large | 1.49 | 1.02 | 1.47 |
| length | small | 0.91 | 2.63 | 0.35 |
| length | medium | 0.92 | 2.62 | 0.35 |
| length | large | 0.92 | 2.63 | 0.35 |
| to_list | small | 400 | 20.3 | 19.67 |
| to_list | medium | 32833 | 2810 | 11.68 |
| to_list | large | 2280000 | 254910 | 8.94 |
| pop | small | 2.13 | 10.9 | 0.20 |
| pop | medium | 2.11 | 10.7 | 0.20 |
| pop | large | 2.13 | 10.9 | 0.20 |
| new | small | 0.99 | 1.01 | 0.97 |
| new | medium | 0.95 | 1.02 | 0.93 |
| new | large | 0.96 | 1.01 | 0.95 |

### Simple queue

Worst ratio 1.40.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | 8.01 | 10.7 | 0.75 |
| put | medium | 7.84 | 11.1 | 0.71 |
| put | large | 8.12 | 10.6 | 0.77 |
| peek | small | 3.40 | 3.48 | 0.98 |
| peek | medium | 3.48 | 3.43 | 1.01 |
| peek | large | 3.37 | 3.41 | 0.99 |
| qsize | small | 0.99 | 2.79 | 0.36 |
| qsize | medium | 0.99 | 2.74 | 0.36 |
| qsize | large | 0.98 | 2.73 | 0.36 |
| to_list | small | 681 | 639 | 1.07 |
| to_list | medium | 50000 | 45867 | 1.09 |
| to_list | large | 3120000 | 2925580 | 1.07 |
| get | small | 13.3 | 9.52 | 1.40 |
| get | medium | 9.73 | 9.51 | 1.02 |
| get | large | 12.1 | 11.2 | 1.07 |
| new | small | 0.99 | 1.22 | 0.81 |
| new | medium | 1.01 | 1.23 | 0.82 |
| new | large | 1.00 | 1.23 | 0.81 |

### Priority queue

Worst ratio 5.54.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | 19.0 | 9.19 | 2.06 |
| put | medium | 19.0 | 9.13 | 2.08 |
| put | large | 21.5 | 9.28 | 2.32 |
| peek | small | 1.00 | 1.00 | 1.00 |
| peek | medium | 1.00 | 1.00 | 1.00 |
| peek | large | 0.99 | 0.99 | 1.00 |
| qsize | small | 0.98 | 2.75 | 0.36 |
| qsize | medium | 0.98 | 2.74 | 0.36 |
| qsize | large | 0.97 | 2.70 | 0.36 |
| from_list | small | 118 | 48.3 | 2.45 |
| from_list | medium | 117 | 48.6 | 2.41 |
| from_list | large | 121 | 48.9 | 2.47 |
| to_sorted_list | small | 2260 | 475 | 4.76 |
| to_sorted_list | medium | 308750 | 55740 | 5.54 |
| to_sorted_list | large | 16200000 | 3303000 | 4.90 |
| get | small | 64.8 | 14.8 | 4.37 |
| get | medium | 125 | 30.9 | 4.04 |
| get | large | 188 | 44.7 | 4.21 |
| new | small | 5.62 | 2.46 | 2.28 |
| new | medium | 5.51 | 2.44 | 2.26 |
| new | large | 7.69 | 2.50 | 3.07 |

### Binary heap

Worst ratio 5.56.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 18.8 | 9.25 | 2.03 |
| push | medium | 18.9 | 9.17 | 2.06 |
| push | large | 22.5 | 9.31 | 2.42 |
| peek | small | 1.00 | 1.00 | 1.01 |
| peek | medium | 1.00 | 1.00 | 1.00 |
| peek | large | 1.00 | 0.99 | 1.00 |
| length | small | 0.95 | 2.63 | 0.36 |
| length | medium | 0.95 | 2.62 | 0.36 |
| length | large | 0.95 | 2.64 | 0.36 |
| from_list | small | 118 | 48.7 | 2.43 |
| from_list | medium | 119 | 49.1 | 2.42 |
| from_list | large | 122 | 49.2 | 2.49 |
| to_sorted_list | small | 2250 | 470 | 4.79 |
| to_sorted_list | medium | 306250 | 55128 | 5.56 |
| to_sorted_list | large | 16300000 | 3308200 | 4.93 |
| pop | small | 64.7 | 15.9 | 4.06 |
| pop | medium | 124 | 30.7 | 4.04 |
| pop | large | 192 | 44.1 | 4.35 |
| new | small | 5.66 | 2.36 | 2.40 |
| new | medium | 5.61 | 2.36 | 2.38 |
| new | large | 7.62 | 2.39 | 3.19 |

### Doubly linked list

Worst ratio 12.40.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | 11.8 | 4.23 | 2.78 |
| push_front | medium | 11.7 | 4.99 | 2.34 |
| push_front | large | 14.7 | 5.04 | 2.92 |
| push_back | small | 11.7 | 4.43 | 2.65 |
| push_back | medium | 11.7 | 4.86 | 2.41 |
| push_back | large | 14.7 | 5.12 | 2.87 |
| insert_before | small | 17.7 | 3.68 | 4.80 |
| insert_before | medium | 17.5 | 4.63 | 3.78 |
| insert_before | large | 20.9 | 5.66 | 3.69 |
| insert_after | small | 17.4 | 3.74 | 4.66 |
| insert_after | medium | 17.4 | 4.77 | 3.64 |
| insert_after | large | 21.1 | 5.23 | 4.03 |
| get | small | 10.9 | 1.30 | 8.40 |
| get | medium | 10.7 | 1.21 | 8.90 |
| get | large | 15.4 | 1.24 | 12.40 |
| set | small | 1.72 | 1.29 | 1.34 |
| set | medium | 1.58 | 1.17 | 1.35 |
| set | large | 1.62 | 1.19 | 1.36 |
| next | small | 2.73 | 1.68 | 1.62 |
| next | medium | 2.45 | 1.45 | 1.70 |
| next | large | 2.97 | 1.76 | 1.69 |
| prev | small | 2.73 | 1.70 | 1.61 |
| prev | medium | 2.48 | 1.45 | 1.71 |
| prev | large | 3.03 | 1.74 | 1.74 |
| length | small | 0.96 | 2.67 | 0.36 |
| length | medium | 0.95 | 2.63 | 0.36 |
| length | large | 0.94 | 2.63 | 0.36 |
| to_list | small | 197 | 109 | 1.80 |
| to_list | medium | 5443 | 4350 | 1.25 |
| to_list | large | 74755 | 71905 | 1.04 |
| remove | small | 5.98 | 6.85 | 0.87 |
| remove | medium | 6.97 | 6.51 | 1.07 |
| remove | large | 8.03 | 7.72 | 1.04 |
| new | small | 12.0 | 2.44 | 4.90 |
| new | medium | 12.0 | 2.45 | 4.88 |
| new | large | 14.5 | 2.44 | 5.95 |

### List iterator

Worst ratio 3.86.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| iter_first | small | 4.45 | 3.20 | 1.39 |
| iter_first | medium | 4.45 | 3.18 | 1.40 |
| iter_first | large | 4.44 | 3.19 | 1.39 |
| iter_last | small | 4.16 | 3.33 | 1.25 |
| iter_last | medium | 4.18 | 3.34 | 1.25 |
| iter_last | large | 4.18 | 3.32 | 1.26 |
| next | small | 6.78 | 1.76 | 3.86 |
| next | medium | 6.58 | 1.77 | 3.72 |
| next | large | 6.57 | 1.82 | 3.62 |
| previous | small | 5.89 | 2.02 | 2.92 |
| previous | medium | 5.76 | 1.87 | 3.07 |
| previous | large | 5.80 | 1.87 | 3.11 |
| set | small | 1.00 | 1.01 | 0.99 |
| set | medium | 1.01 | 1.00 | 1.01 |
| set | large | 0.99 | 1.02 | 0.97 |
| add | small | 15.4 | 5.71 | 2.70 |
| add | medium | 15.6 | 5.67 | 2.75 |
| add | large | 15.5 | 5.70 | 2.71 |
| remove | small | 15.5 | 5.70 | 2.71 |
| remove | medium | 15.4 | 5.65 | 2.73 |
| remove | large | 15.5 | 5.73 | 2.70 |
| has_next | small | 1.00 | 1.01 | 0.98 |
| has_next | medium | 1.00 | 1.02 | 0.98 |
| has_next | large | 0.99 | 0.99 | 1.00 |
| has_previous | small | 0.97 | 1.01 | 0.97 |
| has_previous | medium | 0.99 | 1.00 | 0.98 |
| has_previous | large | 0.97 | 1.02 | 0.95 |
| position | small | 0.97 | 1.00 | 0.97 |
| position | medium | 0.97 | 1.01 | 0.96 |
| position | large | 0.96 | 1.01 | 0.95 |
| finish | small | 4.41 | 3.20 | 1.38 |
| finish | medium | 4.43 | 3.20 | 1.38 |
| finish | large | 4.42 | 3.19 | 1.39 |

### Tree map

Worst ratio 26.52.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| insert | small | 72.9 | 24.6 | 2.97 |
| insert | medium | 144 | 62.4 | 2.30 |
| insert | large | 257 | 147 | 1.75 |
| remove | small | 357 | 54.4 | 6.56 |
| remove | medium | 548 | 118 | 4.63 |
| remove | large | 784 | 221 | 3.55 |
| lookup | small | 67.1 | 16.0 | 4.18 |
| lookup | medium | 136 | 37.8 | 3.60 |
| lookup | large | 258 | 83.0 | 3.11 |
| contains | small | 56.5 | 18.1 | 3.12 |
| contains | medium | 122 | 38.2 | 3.19 |
| contains | large | 229 | 84.6 | 2.70 |
| min | small | 14.3 | 1.48 | 9.62 |
| min | medium | 14.2 | 3.59 | 3.95 |
| min | large | 14.4 | 5.88 | 2.45 |
| max | small | 14.2 | 1.49 | 9.57 |
| max | medium | 14.3 | 2.23 | 6.39 |
| max | large | 14.4 | 4.89 | 2.94 |
| lower_bound | small | 72.0 | 17.2 | 4.19 |
| lower_bound | medium | 143 | 37.6 | 3.80 |
| lower_bound | large | 263 | 83.4 | 3.15 |
| range | small | 221 | 30.0 | 7.36 |
| range | medium | 13974 | 814 | 17.16 |
| range | large | 144940 | 7059 | 20.53 |
| to_list | small | 995 | 44.4 | 22.43 |
| to_list | medium | 81333 | 3067 | 26.52 |
| to_list | large | 3525000 | 195888 | 18.00 |
| length | small | 0.95 | 2.66 | 0.36 |
| length | medium | 0.95 | 2.65 | 0.36 |
| length | large | 0.94 | 2.64 | 0.36 |
| new | small | 30.3 | 2.33 | 13.00 |
| new | medium | 30.3 | 2.36 | 12.86 |
| new | large | 29.5 | 2.38 | 12.38 |

### Bitset

Worst ratio 3.32.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 1.45 | 1.27 | 1.14 |
| set | medium | 1.29 | 1.14 | 1.13 |
| set | large | 1.29 | 1.15 | 1.12 |
| clear | small | 1.42 | 1.27 | 1.12 |
| clear | medium | 1.29 | 1.15 | 1.12 |
| clear | large | 1.29 | 1.14 | 1.14 |
| get | small | 1.59 | 1.32 | 1.20 |
| get | medium | 1.48 | 1.19 | 1.25 |
| get | large | 1.48 | 1.18 | 1.25 |
| count | small | 11.6 | 3.90 | 2.98 |
| count | medium | 290 | 184 | 1.58 |
| count | large | 15118 | 11859 | 1.27 |
| length | small | 0.95 | 2.66 | 0.36 |
| length | medium | 0.94 | 2.63 | 0.36 |
| length | large | 0.95 | 2.64 | 0.36 |
| to_list | small | 151 | 61.6 | 2.46 |
| to_list | medium | 8357 | 3821 | 2.19 |
| to_list | large | 806667 | 242773 | 3.32 |
| union | small | 1.11 | 1.02 | 1.08 |
| union | medium | 48.6 | 48.0 | 1.01 |
| union | large | 2695 | 2894 | 0.93 |
| intersection | small | 1.11 | 1.14 | 0.98 |
| intersection | medium | 49.0 | 48.6 | 1.01 |
| intersection | large | 2765 | 2930 | 0.94 |
| difference | small | 1.30 | 1.12 | 1.16 |
| difference | medium | 48.4 | 48.7 | 1.00 |
| difference | large | 2773 | 2896 | 0.96 |
| xor | small | 1.33 | 1.01 | 1.32 |
| xor | medium | 48.0 | 48.1 | 1.00 |
| xor | large | 2716 | 2896 | 0.94 |
| new | small | 2.52 | 8.86 | 0.28 |
| new | medium | 2.47 | 9.39 | 0.26 |
| new | large | 2.48 | 9.19 | 0.27 |

### Bit list

Worst ratio 5.66.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 3.75 | 2.46 | 1.53 |
| push | medium | 3.78 | 2.45 | 1.54 |
| push | large | 3.87 | 2.46 | 1.57 |
| get | small | 1.80 | 1.32 | 1.37 |
| get | medium | 1.68 | 1.20 | 1.41 |
| get | large | 1.68 | 1.18 | 1.42 |
| set | small | 2.05 | 1.28 | 1.60 |
| set | medium | 1.91 | 1.15 | 1.66 |
| set | large | 1.94 | 1.17 | 1.66 |
| length | small | 1.01 | 2.89 | 0.35 |
| length | medium | 1.00 | 2.83 | 0.35 |
| length | large | 0.95 | 2.77 | 0.34 |
| count | small | 7.03 | 3.39 | 2.08 |
| count | medium | 332 | 189 | 1.76 |
| count | large | 21400 | 12072 | 1.77 |
| to_list | small | 198 | 35.0 | 5.66 |
| to_list | medium | 9850 | 2145 | 4.59 |
| to_list | large | 622500 | 137825 | 4.52 |
| pop | small | 3.87 | 2.05 | 1.88 |
| pop | medium | 5.73 | 2.78 | 2.06 |
| pop | large | 3.87 | 2.07 | 1.87 |
| new | small | 5.61 | 9.09 | 0.62 |
| new | medium | 5.66 | 9.20 | 0.62 |
| new | large | 5.57 | 9.14 | 0.61 |

### Hash map

Worst ratio 21.75.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 9.57 | 2.24 | 4.27 |
| set | medium | 10.5 | 2.26 | 4.63 |
| set | large | 13.3 | 2.75 | 4.86 |
| get | small | 22.7 | 1.51 | 15.04 |
| get | medium | 22.0 | 1.36 | 16.16 |
| get | large | 34.6 | 1.59 | 21.75 |
| has | small | 9.92 | 1.26 | 7.86 |
| has | medium | 8.82 | 1.27 | 6.97 |
| has | large | 10.8 | 1.46 | 7.42 |
| pop | small | 25.1 | 2.75 | 9.14 |
| pop | medium | 29.7 | 2.71 | 10.94 |
| pop | large | 36.3 | 3.40 | 10.68 |
| size | small | 1.00 | 2.41 | 0.41 |
| size | medium | 1.00 | 2.47 | 0.40 |
| size | large | 1.01 | 2.46 | 0.41 |
| keys | small | 262 | 51.1 | 5.13 |
| keys | medium | 14462 | 2776 | 5.21 |
| keys | large | 142361 | 23106 | 6.16 |
| build | small | 1668 | 245 | 6.80 |
| build | medium | 120833 | 15411 | 7.84 |
| build | large | 1113095 | 133866 | 8.31 |

### LRU cache

Worst ratio 10.74.

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| add | small | 14.7 | 9.38 | 1.56 |
| add | medium | 15.9 | 10.0 | 1.59 |
| add | large | 36.6 | 23.7 | 1.54 |
| get | small | 18.0 | 10.4 | 1.73 |
| get | medium | 19.0 | 11.7 | 1.62 |
| get | large | 31.9 | 37.4 | 0.85 |
| peek | small | 25.0 | 9.76 | 2.56 |
| peek | medium | 26.5 | 9.73 | 2.72 |
| peek | large | 42.9 | 22.1 | 1.94 |
| contains | small | 14.2 | 1.41 | 10.06 |
| contains | medium | 13.4 | 1.25 | 10.74 |
| contains | large | 18.3 | 1.99 | 9.20 |
| remove | small | 36.4 | 12.4 | 2.94 |
| remove | medium | 41.7 | 11.4 | 3.67 |
| remove | large | 90.4 | 25.8 | 3.51 |
| purge | small | 1343 | 263 | 5.11 |
| purge | medium | 91346 | 20142 | 4.54 |
| purge | large | 7520833 | 1649188 | 4.56 |
| resize | small | 1029 | 209 | 4.92 |
| resize | medium | 85417 | 17743 | 4.81 |
| resize | large | 6833333 | 1078521 | 6.34 |
| keys | small | 644 | 84.4 | 7.63 |
| keys | medium | 39000 | 10958 | 3.56 |
| keys | large | 298611 | 87712 | 3.40 |
| len | small | 0.98 | 2.72 | 0.36 |
| len | medium | 0.99 | 2.69 | 0.37 |
| len | large | 0.97 | 2.70 | 0.36 |
| new | small | 18.6 | 8.18 | 2.28 |
| new | medium | 18.7 | 8.50 | 2.19 |
| new | large | 24.1 | 9.14 | 2.64 |
| capacity | small | 1.98 | 2.76 | 0.72 |
| capacity | medium | 1.96 | 2.73 | 0.72 |
| capacity | large | 1.99 | 2.69 | 0.74 |
| set_lifetime | small | 3.23 | 6.17 | 0.52 |
| set_lifetime | medium | 3.23 | 6.12 | 0.53 |
| set_lifetime | large | 3.24 | 6.10 | 0.53 |
| metrics | small | 10.2 | 6.38 | 1.60 |
| metrics | medium | 10.3 | 6.40 | 1.60 |
| metrics | large | 10.3 | 6.43 | 1.60 |
| expiry | small | 39.6 | 7.67 | 5.16 |
| expiry | medium | 39.7 | 8.46 | 4.69 |
| expiry | large | 70.6 | 22.3 | 3.16 |
| remove_seq | small | 7.30 | 3.13 | 2.33 |
| remove_seq | medium | 14.5 | 6.21 | 2.33 |
| remove_seq | large | 19.4 | 13.4 | 1.45 |
| purge_isolated | small | 97.7 | 50.7 | 1.93 |
| purge_isolated | medium | 1268 | 931 | 1.36 |
| purge_isolated | large | | | not timeable |
| resize_isolated | small | 375 | 86.7 | 4.32 |
| resize_isolated | medium | 8341 | 2294 | 3.64 |
| resize_isolated | large | 50781 | 19636 | 2.59 |

## Hash map vs Base.Map

Both sides are Bend: the hash map of `src/containers/hash_table.bend` against
the standard library's `Base.Map` (a crit-bit tree over String keys), on the
same operations, String keys and inputs, with identical checksums. Same
differential method as the containers. **Ratio = HashMap time / Base.Map time**:
below 1 the hash map is faster. `Base.Map.size` walks the tree, so the
hash map's O(1) size is compared against an O(n) walk. See
`benchmarks/maps/compare.py`.

| Operation | Size | HashMap (ns) | Base.Map (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | 64 | 10.3 | 259 | 0.04 |
| set | 4096 | 11.4 | 533 | 0.02 |
| set | 262144 | 13.6 | 980 | 0.01 |
| get | 64 | 15.0 | 114 | 0.13 |
| get | 4096 | 14.2 | 249 | 0.06 |
| get | 262144 | 20.8 | 565 | 0.04 |
| has | 64 | 9.92 | 111 | 0.09 |
| has | 4096 | 8.79 | 254 | 0.03 |
| has | 262144 | 10.7 | 598 | 0.02 |
| pop | 64 | 25.7 | 364 | 0.07 |
| pop | 4096 | 30.6 | 760 | 0.04 |
| pop | 262144 | 39.4 | 1433 | 0.03 |
| size | 64 | 1.00 | 188 | 0.01 |
| size | 4096 | | | not timeable |
| size | 262144 | | | not timeable |
| keys | 64 | 264 | 999 | 0.26 |
| keys | 4096 | 14267 | 67133 | 0.21 |
| keys | 32768 | 124405 | 530060 | 0.23 |
| build | 64 | 1750 | 9441 | 0.19 |
| build | 4096 | 122619 | 1040476 | 0.12 |
| build | 32768 | 1148810 | 9937500 | 0.12 |

