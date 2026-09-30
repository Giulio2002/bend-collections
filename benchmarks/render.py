#!/usr/bin/env python3
"""Render BENCHMARK.md from build/bench/full.json (full_sweep.py) and
build/bench/crypto.json (crypto.py).

  python3 benchmarks/render.py
"""
import json, platform, statistics, subprocess, sys
from collections import OrderedDict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
from workloads import TABLE  # noqa: E402

NAMES = OrderedDict([
    ('dynamic_array', 'Dynamic array'), ('deque', 'Deque'), ('queue', 'FIFO queue'), ('stack', 'Stack'),
    ('simple_queue', 'Simple queue'), ('priority_queue', 'Priority queue'),
    ('binary_heap', 'Binary heap'), ('doubly_linked_list', 'Doubly linked list'),
    ('dlist_iterator', 'List iterator'), ('balanced_search_tree', 'Tree map'), ('bitset', 'Bitset'), ('bitlist', 'Bit list'),
    ('hash_table', 'Hash map'), ('lru', 'LRU cache')])
HASHES = OrderedDict([
    ('sha256', ('SHA-256', 'portable FIPS 180-4 C (`benchmarks/native/sha256.c`)')),
    ('keccak256', ('Keccak-256', 'XKCP `plain-64bits` fully unrolled (`benchmarks/native/xkcp/`)')),
    ('blake2s', ('BLAKE2s', 'official BLAKE2 reference `blake2s-ref.c`')),
    ('blake2b', ('BLAKE2b', 'official BLAKE2 reference `blake2b-ref.c`')),
    ('blake3', ('BLAKE3', 'official BLAKE3 C, portable only (no SIMD)')),
])


def load(p):
    p = ROOT / p
    return json.loads(p.read_text()) if p.exists() else None


def ns(x):
    if x is None:
        return '-'
    return '%.0f' % x if x >= 100 else '%.1f' % x if x >= 10 else '%.2f' % x


def per_op(row, key):
    d = row.get(key)
    if not d or not row.get('operations_per_sample'):
        return None
    return statistics.median(d) / row['operations_per_sample']


def intrusive_section(rep):
    """Application-owned lists (benchmarks/intrusive.py): the same entity
    workloads through the intrusive list, the handle DList and C."""
    out = ['### Intrusive doubly linked list', '',
           'Entity workloads from `benchmarks/intrusive.py` (contributed in',
           '[#5](https://github.com/Giulio2002/bend-collections/pull/5)): **transfer** removes an',
           'entity from one list and prepends it to another; **pulses** is a pooled',
           'lifecycle. The same application-owned entity array drives the intrusive list',
           '(links inside the entities), the handle-checked `DList`, and C. Every run',
           'must produce the reference checksum; the hot loops allocate nothing (checked',
           'with positive controls). Median of the samples, nanoseconds per unit.', '']
    if not rep:
        return out + ['(not measured yet)', '']
    out += ['| Workload | Entities | Intrusive (ns) | DList (ns) | C (ns) | Intrusive / C | DList / Intrusive |',
            '|---|---:|---:|---:|---:|---:|---:|']
    for r in rep['rows']:
        m = r['metrics']
        i, d, c = (m[k]['median_ns_per_unit'] for k in ('intrusive', 'dlist', 'c'))
        out.append('| %s | %d | %.2f | %.2f | %.2f | %.2f | %.1f |' % (r['workload'], r['size'], i, d, c, i / c, d / i))
    return out + ['']


# ---- crypto_suite.py groups ----
# case -> (title, C reference, first column, unit); unit 'us' per operation or 'ns' per draw
SUITE = OrderedDict([
    ('hash', ('More hashes', 'build/bench/suite-hash.json', [
        ('sha512', 'SHA-512', 'Monocypher 4.0.2 `crypto_sha512` (portable C)', 'Message', 'us'),
        ('sha3_256', 'SHA3-256', 'XKCP `plain-64bits` Keccak-p[1600] with the FIPS 202 padding', 'Message', 'us'),
        ('hasher', 'Incremental hashing (`Hasher`)', 'the same C as the one-shot rows through init/update/final '
         '(`sha256_ctx.h`, Monocypher `crypto_sha512_*`, `sha3_ctx.h` over XKCP), fed the same chunks. '
         '"one-shot" is `hash.sha256`/`sha512`/`sha3_256` of the whole message; "64 B chunks" is '
         '`new_*`, `update_all` over 64-byte pieces cut before the timed region, then `digest`', 'Hash, message, feed', 'us'),
        ('subtle_eq', '`subtle.eq`', 'constant-time loop (lengths, then OR of the XOR of every byte pair, no early exit); '
         'equal inputs, so every byte is compared', 'Length', 'us'),
        ('hmac_sha256', 'HMAC-SHA256', 'RFC 2104 over the portable FIPS 180-4 SHA-256 (`benchmarks/native/sha256_ctx.h`), 32-byte key', 'Message', 'us'),
        ('hkdf_sha256', 'HKDF-SHA256', 'RFC 5869 over the same C HMAC; 32-byte input keying material, 32-byte salt, 16-byte info', 'Output', 'us'),
    ])),
    ('cipher', ('Ciphers and AEADs', 'build/bench/suite-cipher.json', [
        ('chacha20', 'ChaCha20', 'Monocypher 4.0.2 `crypto_chacha20_ietf` (portable C)', 'Message', 'us'),
        ('poly1305', 'Poly1305', 'Monocypher 4.0.2 `crypto_poly1305` (portable C)', 'Message', 'us'),
        ('chacha20poly1305', 'ChaCha20-Poly1305', 'Monocypher 4.0.2 `crypto_aead_init_ietf` + `crypto_aead_write`/`_read`', 'Message', 'us'),
        ('xchacha20poly1305', 'XChaCha20-Poly1305', 'Monocypher 4.0.2 `crypto_aead_lock`/`_unlock`', 'Message', 'us'),
        ('aes128gcm', 'AES-128-GCM', 'BearSSL `br_gcm` with the constant-time bitsliced `br_aes_ct64` and `br_ghash_ctmul64` '
         '(the "C ct" column); the "C table" column swaps in the table-based `br_aes_big` (not constant-time)', 'Message', 'us'),
        ('aes256gcm', 'AES-256-GCM', 'as AES-128-GCM, with a 32-byte key', 'Message', 'us'),
    ])),
    ('pk', ('Public-key and password hashing', 'build/bench/suite-pk.json', [
        ('x25519', 'X25519 shared secret', 'Monocypher 4.0.2 `crypto_x25519`', 'Operation', 'us'),
        ('ed25519_keygen', 'Ed25519 key generation', 'Monocypher 4.0.2 `crypto_ed25519_key_pair` (SHA-512)', 'Operation', 'us'),
        ('ed25519_sign', 'Ed25519 sign', 'Monocypher 4.0.2 `crypto_ed25519_sign`', 'Message', 'us'),
        ('ed25519_verify', 'Ed25519 verify', 'Monocypher 4.0.2 `crypto_ed25519_check`', 'Message', 'us'),
        ('argon2id', 'Argon2id', 'the official P-H-C reference (`ref.c`, portable, no SSE), one thread', 'Parameters', 'us'),
        ('secp256k1', 'secp256k1 (ECDSA, recovery, BIP-340)', 'libsecp256k1 v0.6.0 (precomputed tables, 5x52 field, no assembly; '
         'recovery, extrakeys and schnorrsig modules); the Bend side is `src/crypto/secp256k1.bend` (#26)', 'Operation', 'us'),
    ])),
    ('random', ('Random', 'build/bench/suite-random.json', [
        ('chacha8_uint64', 'ChaCha8 `uint64`', 'a C transcription of Go 1.23 `internal/chacha8rand` (portable block function)', 'Draws', 'ns'),
        ('pcg_uint64', 'PCG `uint64`', 'a C transcription of Go 1.23 `math/rand/v2` PCG-DXSM', 'Draws', 'ns'),
        ('uint_below', '`uint_below` (ChaCha8)', "Go's `uint64n` (Lemire) transcribed", 'Bound', 'ns'),
        ('float64', '`float64` (ChaCha8)', "Go's `Float64` transcribed", 'Draws', 'ns'),
        ('shuffle', '`shuffle` (ChaCha8)', "Go's Fisher-Yates `Shuffle` on a C array; Bend's `shuffle_array` on an `Array<U32>`, in place", 'Items', 'us'),
        ('crypto_random_bytes', '`crypto.random.bytes`', "Go's `ChaCha8.Read` transcribed; Bend returns a list of bytes", 'Request', 'us'),
        ('crypto_random_read', '`crypto.random.read_words`', "Go's `ChaCha8.Read` transcribed; Bend writes the bytes packed into an `Array<U32>`, in place", 'Request', 'us'),
    ])),
])
TODO_ROWS = {}   # case -> text, for a module that could not be measured


def fmt_unit(us, unit):
    return ns(us * 1000 if unit == 'ns' else us)


def suite_tables(worst):
    """the sections for the crypto_suite.py groups; worst[title] = worst ratio"""
    out = []
    for group, (heading, path, cases) in SUITE.items():
        rep = load(path)
        out += ['## %s' % heading, '']
        if group == 'hash':
            out += ['Same method as the hashes above (`benchmarks/crypto_suite.py --group hash`).', '']
        elif group == 'pk':
            out += ['A curve operation takes Bend 0.1-1 s, so these rows time a few operations',
                    'per sample (Argon2id: 64 hashes at 64 KiB, one at 19 MiB). The curve C',
                    'references repeat their timed pass until 50 ms have passed and report the',
                    'mean pass. Microseconds per operation.', '']
        elif group == 'random':
            out += ['Fixed seeds (ChaCha8: bytes `7i + 1`; PCG: `NewPCG(1, 2)`); every draw is stored',
                    'and folded into the checksum after the timed region. Nanoseconds per draw, or',
                    'microseconds per shuffle / per request.', '']
        for name, title, ref, col, unit in cases:
            rows = [r for r in (rep or {}).get('rows', []) if r['case'] == name]
            if not rows:
                if name in TODO_ROWS:
                    out += ['### %s' % title, '', 'C reference: %s.' % ref, '', '**TODO:** %s' % TODO_ROWS[name], '']
                    worst[title] = None
                continue
            w = max(r['ratio'] for r in rows if r['ratio'])
            worst[title] = w
            alt = any('ratio_alt' in r for r in rows)
            out += ['### %s' % title, '', 'C reference: %s. Worst ratio %.2f.' % (ref, w), '']
            u = unit
            if alt:
                out += ['| %s | Bend (%s) | C ct (%s) | Ratio | C table (%s) | Ratio vs table |' % (col, u, u, u),
                        '|---:|---:|---:|---:|---:|---:|']
            else:
                out += ['| %s | Bend (%s) | C (%s) | Ratio |' % (col, u, u), '|---:|---:|---:|---:|']
            for r in rows:
                b, c = r['us_per_op']['bend'], r['us_per_op']['c']
                line = '| %s | %s | %s | %.2f |' % (r['label'], fmt_unit(b, u), fmt_unit(c, u), r['ratio'])
                if alt:
                    line += ' %s | %.2f |' % (fmt_unit(r['us_per_op']['c_alt'], u), r['ratio_alt'])
                out.append(line)
            out.append('')
    return out


def references_section():
    return ['## C references', '',
            'Every reference is portable C compiled with `-O3 -march=native -std=c11`: no',
            'assembly, no intrinsics, no AES/SHA/PMULL instructions (the compiler may still',
            'auto-vectorize). Vendored sources are unmodified; each directory has its licence',
            'and a REVISION file.', '',
            '| Reference | Version | Licence | Used for | Timing behaviour |', '|---|---|---|---|---|',
            '| `benchmarks/native/sha256.c`, `sha256_ctx.h` | written for this repo (FIPS 180-4, RFC 2104, RFC 5869) | MIT (this repo) | SHA-256, incremental SHA-256, HMAC-SHA256, HKDF-SHA256 | constant-time (no secret-indexed tables) |',
            '| XKCP `plain-64bits` (`benchmarks/native/xkcp/`) | commit eb5244d6 | CC0 | Keccak-256, SHA3-256 (+ `sha3_ctx.h` sponge) | constant-time |',
            '| BLAKE2 reference (`benchmarks/native/blake/`) | commit ed1974ea | CC0 / Apache-2.0 | BLAKE2s, BLAKE2b | constant-time |',
            '| BLAKE3 C, portable only (`benchmarks/native/blake/`) | commit 6aab490a | CC0 / Apache-2.0 | BLAKE3 | constant-time |',
            '| Monocypher (`benchmarks/native/monocypher/`) | 4.0.2 (commit 0d85f98c) | BSD-2-Clause / CC0 | SHA-512, ChaCha20, Poly1305, (X)ChaCha20-Poly1305, X25519, Ed25519 | constant-time |',
            '| BearSSL (`benchmarks/native/bearssl/`) | commit 7bea48e5 (2026-04-06) | MIT | AES-GCM: `aes_ct64` + `ghash_ctmul64` (C ct), `aes_big` (C table) | ct64/ctmul64 constant-time (bitsliced, 4 blocks at a time); `aes_big` table lookups, **not** constant-time |',
            '| Argon2 reference (`benchmarks/native/argon2/`) | P-H-C phc-winner-argon2 commit f57e61e1 (2021-06-25) | CC0 / Apache-2.0 | Argon2id | `ref.c`, portable; data-independent addressing in the first half-pass as the RFC specifies |',
            '| libsecp256k1 (`benchmarks/native/secp256k1/`) | v0.6.0 (commit 0cdc758a) | MIT | secp256k1 | constant-time signing |',
            '| `benchmarks/native/gorand.h` | transcription of Go 1.23 `internal/chacha8rand` and `math/rand/v2` (pcg.go, rand.go, chacha8.go) | BSD-3-Clause (Go) | ChaCha8, PCG, `uint_below`, `float64`, shuffle, `crypto.random.bytes` | portable block function (Go itself uses SIMD) |',
            '| `suite_subtle_eq.c` | written for this repo | MIT (this repo) | `subtle.eq` | constant-time loop |',
            '',
            'Fairness notes:', '',
            '- Bend runs single-threaded (`--threads 1`) on byte lists (one U32 per byte);',
            '  C works on byte arrays in place. Input parsing and message cutting happen',
            '  before the timed region on both sides; the checksum after it.',
            '- The Bend AES is constant-time (the Boyar-Peralta S-box circuit on one byte at',
            '  a time, GHASH bit by bit). The fair column is BearSSL `aes_ct64`; the table',
            '  column shows what a non-constant-time C costs.',
            '- AES-GCM and the AEADs set up the key for every message on both sides (the',
            '  Bend API takes the key bytes per call).',
            '- Ed25519 sign: the Bend API takes the 32-byte seed and derives the public key',
            '  inside every call; Monocypher\'s `crypto_ed25519_sign` takes the 64-byte',
            '  expanded secret key (seed || public key), so it skips one fixed-base',
            '  scalar multiplication per signature.',
            '- secp256k1: libsecp256k1 is production code with precomputed multiplication',
            '  tables, not a plain reference; its verify parses the key and signature inside',
            '  the timed region (the Bend API takes bytes) and normalises s (Bend\'s verify',
            '  accepts high s). Bend\'s BIP-340 sign derives the public key on every call.',
            '  No Python check (Bend and C must agree; RFC 6979 and fixed BIP-340 aux make',
            '  both deterministic).',
            '- Shuffle: both sides shuffle the first n slots of an array in place (Bend:',
            '  `shuffle_array` on an `Array<U32>` of 2^d >= n slots, filled before the timed',
            '  region; the list `shuffle` writes the list into such an array and reads it',
            '  back, two more linear passes).', '']


def main():
    full, crypto = load('build/bench/full.json'), load('build/bench/crypto.json')
    maths = load('build/bench/math.json')
    typed = load('build/bench/typed.json')
    out = ['# Benchmarks', '',
           'Every row runs the same algorithm in Bend (native C backend, one thread) and in C',
           '(`-O3 -march=native`), with identical inputs, and the two results must agree',
           '(a checksum of every result, or the full digests). **Ratio = Bend time / C time**:',
           'below 1 Bend is faster.', '']
    env = (full or {}).get('environment', {})
    out += ['Machine: %s, %s. Measured while other work was running on the machine, so' % (platform.machine(), platform.platform()),
            'absolute times are noisy; each sample alternates Bend and C under the same load,',
            'so the ratios are the meaningful column.', '']
    tc = crypto or load('build/bench/suite-hash.json') or {}
    if tc:
        pin = json.loads((ROOT / 'tools/toolchain.json').read_text())['version']
        out += ['Toolchain: Bend %s (the release pinned in `tools/toolchain.json`), every table' % pin, 'measured with it; C: %s.' % tc.get('cc', 'cc'), '']
    out += ['Reproduce:', '', '```sh', 'python3 benchmarks/full_sweep.py --report build/bench/full.json   # containers',
            'python3 benchmarks/crypto.py --report build/bench/crypto.json      # hashes',
            'python3 benchmarks/natural.py --report build/bench/math.json       # math',
            'python3 benchmarks/typed.py --report build/bench/typed.json        # math per type',
            'python3 benchmarks/maps/compare.py --report build/bench/maps.json  # HashMap vs Base.Map',
            'python3 benchmarks/intrusive.py --report build/bench/intrusive.json # intrusive list',
            'python3 benchmarks/crypto_suite.py --group hash   --report build/bench/suite-hash.json',
            'python3 benchmarks/crypto_suite.py --group cipher --report build/bench/suite-cipher.json',
            'python3 benchmarks/crypto_suite.py --group pk     --report build/bench/suite-pk.json',
            'python3 benchmarks/crypto_suite.py --group random --report build/bench/suite-random.json',
            'python3 benchmarks/render.py                                        # this file', '```', '',
            'On the maintainer\'s Mac every command runs through `bench-local` (one run at a',
            'time, never alongside a proof check).', '']
    summary_at = len(out)
    worst = OrderedDict()

    # ---- hashes ----
    out += ['## Hashes', '',
            'Median of five alternating samples per size, after a warm-up; inputs prepared',
            'before the timed region. Microseconds per hash.', '']
    if crypto:
        for algo, (title, ref) in HASHES.items():
            rows = [r for r in crypto['rows'] if r['algorithm'] == algo]
            if not rows:
                continue
            w = max(r['ratio'] for r in rows if r['ratio'])
            worst[title] = w
            out += ['### %s' % title, '', 'C reference: %s. Worst ratio %.2f.' % (ref, w), '',
                    '| Message | Bend (us) | C (us) | Ratio |', '|---:|---:|---:|---:|']
            for r in rows:
                b = r['bytes']
                size = '%d B' % b if b < 1024 else '%d KiB' % (b // 1024) if b < 1048576 else '%d MiB' % (b // 1048576)
                out.append('| %s | %s | %s | %.2f |' % (size, ns(r['us_per_hash']['bend']), ns(r['us_per_hash']['c']), r['ratio']))
            out.append('')
    else:
        out += ['(not measured yet)', '']

    out += suite_tables(worst)
    out += references_section()

    # ---- math ----
    out += ['## Math', '',
            '`src/math/natural.bend` against idiomatic C (`benchmarks/native/math.c`: Euclid',
            'with `%`, `sqrt` plus an integer correction, `__builtin_clzll`, binary',
            'exponentiation, extended Euclid). Each row makes COUNT calls on arguments from',
            'the same MINSTD stream and folds every result into a checksum that must agree;',
            'the `loop` row is the generator and the fold alone, and is part of every other',
            'row. Median of five alternating samples after a warm-up; nanoseconds per call.', '']
    if maths:
        worst['Math (natural)'] = max(r['ratio'] for r in maths['rows'])
        out += ['| Operation | Bend (ns) | C (ns) | Ratio |', '|---|---:|---:|---:|']
        for r in maths['rows']:
            out.append('| %s | %s | %s | %.2f |' % (r['operation'], ns(r['ns_per_call']['bend']), ns(r['ns_per_call']['c']), r['ratio']))
        out.append('')
    else:
        out += ['(not measured yet)', '']

    # ---- math per type ----
    out += ['### Math per type', '',
            'The templated math of `src/math/generic.bend` instantiated for U32, U64 (two',
            'U32 words) and F32, and the software binary64 of `src/math/f64.bend`, against',
            'C with `uint32_t`, `uint64_t` (a 128-bit product for `mod m`), `float` and',
            '`double` (`benchmarks/native/typed.c`), with the same checked semantics (a',
            'result that does not fit counts as 0) and the same square-and-multiply order',
            'for powers. The F64 rows compare software arithmetic with the hardware FPU;',
            'the rounding, conversion, exponent, neighbour and remainder rows (`f64_floor`',
            'to `f64_nextafter`) compare with libm\'s `floor`, `nearbyint`, `fmod`,',
            '`remainder`, `frexp`, `ldexp` and `nextafter` and a `(uint64_t)` cast.',
            'Same method as above; nanoseconds per call.', '']
    if typed:
        worst['Math per type'] = max(r['ratio'] for r in typed['rows'])
        out += ['| Operation | Bend (ns) | C (ns) | Ratio |', '|---|---:|---:|---:|']
        for r in typed['rows']:
            out.append('| %s | %s | %s | %.2f |' % (r['operation'], ns(r['ns_per_call']['bend']), ns(r['ns_per_call']['c']), r['ratio']))
        out.append('')
    else:
        out += ['(not measured yet)', '']

    irep = load('build/bench/intrusive.json')
    if irep:
        worst['Intrusive doubly linked list'] = max(r['metrics']['intrusive']['median_ns_per_unit'] / r['metrics']['c']['median_ns_per_unit']
                                                    for r in irep['rows'])
    out += intrusive_section(irep)

    # ---- containers ----
    out += ['## Containers', '',
            'Each row measures one public operation at three structure sizes. The time of',
            'an operation is the difference between two regions that run 2k and k of them',
            '(build, settle and teardown cancel); removals are measured in a restoring pair',
            'with the insertion that puts the element back. Nanoseconds per operation,',
            'median of six samples. A sample in which other load interrupted a region (A - B',
            'negative or under the timing minimum) is re-taken, both sides together, up to',
            'four times; failed rows are re-measured with `full_sweep.py --retry-failed`.',
            'See `benchmarks/run.py` for the method.', '',
            '† quick sampling (`BENCH_QUICK=1`): a 20 ms instead of 50 ms minimum difference and',
            'three samples instead of six, several rows in parallel. Expect about ±10% on',
            'those ratios; the unmarked rows use the full method.', '']
    done = {}
    for r in (full or {}).get('benchmarks', []):
        done[(r['operation'], r['workload'])] = r
    by = OrderedDict((k, []) for k in NAMES)
    for t in TABLE:
        by.setdefault(t['structure'], []).append(t)
    pending = 0
    for s, title in NAMES.items():
        rows = by.get(s, [])
        if not rows:
            continue
        ratios = [done[(t['operation'], t['workload'])]['ratio'] for t in rows
                  if done.get((t['operation'], t['workload'])) and done[(t['operation'], t['workload'])].get('ratio') is not None]
        if ratios:
            worst[title] = max(ratios)
        out += ['### %s' % title, '']
        if ratios:
            out += ['Worst ratio %.2f.' % max(ratios), '']
        out += ['| Operation | Size | Bend (ns) | C (ns) | Ratio |', '|---|---:|---:|---:|---:|']
        for t in rows:
            key = (t['operation'], t['workload'])
            r = done.get(key)
            op = t['operation'].split('.', 1)[1]
            if r is None:
                out.append('| %s | %s | | | pending |' % (op, t['workload']))
                pending += 1
            elif r.get('ratio') is None:
                out.append('| %s | %s | | | not timeable |' % (op, t['workload']))
            else:
                out.append('| %s | %s | %s | %s | %.2f%s |' % (op, t['workload'], ns(per_op(r, 'bend_delta_ns')),
                           ns(per_op(r, 'reference_delta_ns')), r['ratio'], ' †' if r.get('quick') else ''))
        out.append('')
    # ---- HashMap vs Base.Map ----
    maps = load('build/bench/maps.json')
    out += ['## Hash map vs Base.Map', '',
            'Both sides are Bend: the hash map of `src/containers/hash_table.bend` against',
            "the standard library's `Base.Map` (a crit-bit tree over String keys), on the",
            'same operations, String keys and inputs, with identical checksums. Same',
            'differential method as the containers. **Ratio = HashMap time / Base.Map time**:',
            'below 1 the hash map is faster. `Base.Map.size` walks the tree, so the',
            'hash map\'s O(1) size is compared against an O(n) walk. See',
            '`benchmarks/maps/compare.py`.', '']
    if maps:
        out += ['| Operation | Size | HashMap (ns) | Base.Map (ns) | Ratio |', '|---|---:|---:|---:|---:|']
        for r in maps['rows']:
            op = r['operation'].split('.', 1)[1]
            if r.get('ratio') is None:
                out.append('| %s | %d | | | not timeable |' % (op, r['size']))
            else:
                out.append('| %s | %d | %s | %s | %.2f%s |' % (op, r['size'], ns(per_op(r, 'bend_delta_ns')),
                           ns(per_op(r, 'reference_delta_ns')), r['ratio'], ' †' if r.get('quick') else ''))
        out.append('')
    else:
        out += ['(not measured yet)', '']
    summary = ['## Worst ratio per module', '',
               'The largest Bend / C ratio of each table below (for AES-GCM, against the',
               'constant-time C). Hash map vs Base.Map compares two Bend structures and is not listed.', '',
               '| Module | Worst ratio |', '|---|---:|']
    for k, v in worst.items():
        summary.append('| %s | %s |' % (k, 'TODO' if v is None else '%.2f' % v))
    out[summary_at:summary_at] = summary + ['']
    if pending:
        out.insert(out.index('## Containers') + 2, '**%d of %d container rows are still being measured; they show as pending.**\n' % (pending, len(TABLE)))
    (ROOT / 'BENCHMARK.md').write_text('\n'.join(out) + '\n')
    print('BENCHMARK.md: %d container rows, %d pending' % (len(done), pending))


if __name__ == '__main__':
    main()
