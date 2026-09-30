# Tools

Everything here is Python (3.10+) and serves development: building the checked
proof files from their sources, validating the containers against independent
oracles, and differential tests. Nothing in `src/` depends on it, and the
committed `.bend` proofs check without it.

## Toolchain

`toolchain.json` pins the Bend build the project is checked with (the 2.0.34
release, installed under `~/.bend/v2.0.34/bend`) by path and SHA-256 (one
binary hash per platform, one Base hash), and `toolchain.py` exposes it to the scripts. Paths may start
with `~`. To use a private copy of the pinned release, set `BEND_HOME` to a
directory holding `.bend/bin/bend` and `.bend/bend2`. To use another compiler
(a development build, say), set `BEND` to it, a path or a name on the PATH, and
optionally `BEND_BASE` to its `base.bend`: every script then uses it, the pin
check warns instead of failing, and reports record the unpinned build. The
benchmark and proof scripts outside `tools/` fall back to `$BEND` or `bend` on
the PATH.

## Proof sources: `.src` files and `generators/mac.py`

Bend proofs repeat long types and argument lists constantly (the TreeMap
invariant alone takes eleven fields). So most proof files are written as a
`.src` file next to the `.bend` it becomes, and `mac.py` expands it:

```sh
python3 tools/generators/mac.py proofs/containers/lru/add.src proofs/containers/lru/add.bend
```

The `.bend` is what the checker checks and what is committed; always
regenerate it after editing the `.src`, never edit such a `.bend` by hand.
A `.src` is ordinary Bend plus these lines:

| Line | Meaning |
|---|---|
| `%def NAME text` | every `$NAME` expands to `text` |
| `%def NAME(a, b) text` | `$NAME(x, y)` expands to `text` with `a`, `b` replaced; arguments split at top-level commas, `<\|x, y\|>` keeps its commas |
| `%tmpl NAME(a, b)` ... `%end` | a multi-line template; a line `%use NAME(x, y)` expands to its lines |
| `a##b` | token pasting inside templates (`N##_c` with `N = put` gives `put_c`) |
| `%include file.src` | imports the `%def`s and templates of another source (paths relative to the including file) |

Macros may use other macros; expansion repeats until nothing changes.
Example, from the TreeMap proofs:

```
%def FT +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: $NL, +pl: $PL, +tg: ST.Tr, +fl: $LN
%def F n, root, lo, hi, free, l, d, nl, pl, tg, fl
%def SH ST.SH{$F}
def size_eq($TK, $FT, +hg: $GF) -> {n == SC.length($E, $EST) : Nat}:
```

To regenerate every proof from its source:

```sh
for f in $(find proofs -name '*.src'); do [ -f "${f%.src}.bend" ] && python3 tools/generators/mac.py "$f" "${f%.src}.bend"; done
```

A `.src` without a `.bend` of the same name holds only shared macros for
`%include` (for example `balanced_search_tree/wrap.src`).

## Generators

Each writes checked Bend files that are committed; rerun it after changing
what it generates from.

| Generator | Writes |
|---|---|
| `generators/intrusive_list.py` | intrusive public module and shared internal implementation; `--check` verifies committed output without rewriting |
| `generators/tree_map.py` | the implementation `src/containers/balanced_search_tree.bend` (state threading lowered into helpers) |
| `generators/tm_state.py` | the TreeMap's shadow, model and invariant (`proofs/containers/balanced_search_tree/state.bend`) |
| `generators/tm_mirror.py` | the TreeMap's mirror of the implementation over shadows (`mirror.bend`) and the proofs that the implementation computes the mirror (`sim.bend`); hand-written heads in `balanced_search_tree/gen/*.part` |
| `generators/tm_gate.py` | the TreeMap's entry point `proof.bend`: one theorem per public operation, restated from the proof modules |
| `generators/hash_table_state.py` | the hash map's invariant (in `hash_table/state.bend`) and its rebuild lemmas (`rebuild.bend`) |
| `generators/lru_state.py` | the LRU's invariant (in `lru/state.bend`, after the generated-section marker) |
| `generators/dll_state.py` | the doubly linked list's shadow, model and invariant (`doubly_linked_list/state.bend`) |
| `generators/trace_data.py` | the trace-refinement module of a structure with Data state (`trace.bend`) |
| `generators/pat_expand.py` | helper: expands overlapping match rows into disjoint ones (the checker only reduces on a row that names the shape) |
| `generators/blake2s_gen.py`, `blake2s_tests.py` | BLAKE2s's unrolled compression, block reads, proof lemmas and test vectors |
| `generators/blake2b_gen.py` | BLAKE2b's lanes, unrolled compression, block reads, proof lemmas and tests |
| `generators/blake3/gen.py`, `proofs.py`, `tests.py` | BLAKE3's compression and block reads, their proof modules, and test vectors from the official C |
| `generators/sha512_gen.py` | SHA-512's implementation (fused rotations, constants computed from the primes, the FIPS-specialized rounds `kr16`..`kr80`/`fips16`, the append-free padding), its conformance proof's enumerations and `fast.bend` (specialized == generic) |
| `generators/sha3_gen.py` | SHA3-256's implementation (17-lane block XOR, padding) and its conformance proof |
| `generators/stream_gen.py` | the streaming cores `src/crypto/{sha,sha512,sha3}/stream.bend` behind `hash.bend`'s one-shot and incremental hashing, their proofs (`proofs/crypto/{sha512,sha3}/stream.bend`, `proofs/crypto/hash/stream256.bend`) and the Hasher glue `proofs/crypto/hash/incremental.bend` |
| `generators/chacha8rand_gen.py` | ChaCha8Rand's unrolled double round, block and four-block group (`src/math/random/chacha8/block.bend`) and their proof against the list-based C2SP specification (`proofs/math/random/chacha8/rounds.bend`) |
| `toposort.py` | reorders the definitions of a Bend file so every callee precedes its callers (Bend has no forward references) |

## Validation and differential tests

| Script | Checks |
|---|---|
| `check_intrusive_proofs.py --bend bend` | regenerate proof sources, clean semantic and concrete-adapter checks, coordinated specification and adapter negative controls |
| `check_intrusive.py --bend bend --cc clang` | intrusive-list proofs, C/JS conformance, examples, semantic mutants and native heap-allocation measurements; see [guide](../INTRUSIVE_LIST.md) |
| `../benchmarks/intrusive.py --bend bend --cc clang` | warmed entity transfers and pooled lifecycles against the public DList API and C; independent oracle, generation-layer diagnostic, A/A control, separate timing/allocation/live-byte binaries, raw samples; [method and results](../benchmarks/INTRUSIVE_LIST.md) |
| `check_random.py [seed]` | `src/math/random.bend` and `src/crypto/random.bend` (driver `build/math/random` from `tests/math/random.bend`): Go's published vectors (ChaCha8, the Read transcript hash, PCG, regressGolden), a Python mirror of Go's math/rand/v2 and C2SP chacha8rand on random keys, seeds and call sequences, the OS-keyed generator, and a chi-square smoke test of `uint64n` |
| `backend_diff.py [--quick] [--only m]` | Bend against itself: every public module on identical seeded random and edge-case inputs through `bend file.bend args`, the C backend and the JavaScript backend; any differing line fails ([findings](../docs/BACKEND_BUGS.md)) |
| `validate.py --report build/validation.json` | every container in `tests/structures.json`: builds `tests/<id>/main.bend`, compares its output with the Python oracle in `tests/support/oracles.py` on functional, boundary, differential and structural scenarios (`scenarios.py`), runs semantic mutants that must be caught (`mutants.py`), and checks the container's proof |
| `check_hash_table.py` | the hash map against a Python dict on random histories (growth, backward-shift deletion, every key kind) |
| `check_lru_spec.py` | the LRU against its executable specification, step by step with a moving clock |
| `lru_diff.py` | the Bend LRU against the C reference and its ASan/UBSan build, bit for bit |
| `check_tree_map.py`, `check_tree_map_mutations.py` | the TreeMap against an ordered-map oracle with red-black invariant checks, and semantic mutants (balance, put, cursors, the node store, the folds) that the refinement proof must reject and the differential histories must catch where they can see them; run by `validate.py` |
| `check_iterators.py`, `check_queue_facades.py`, `check_two_list.py`, `check_two_list_mutations.py`, `check_owned_array.py`, `check_owned_array_guards.py` | the iterators, the queue facades, the two-list deque and queue, and owning arrays against independent oracles |
| `check_math.py` | `src/math/natural.bend` against CPython's `math` on random and edge-case calls, errors included |
| `check_generic.py` | every templated math function (`src/math/generic.bend`) at U32, U64, F32 and F64 against Python, naming the `spec/math/generic.bend` clause of each case |
| `check_f64.py` | the software binary64 (`src/math/f64.bend`) against the machine's doubles on random bit patterns of every class and rounding ties |
| `check_f64_spec.py` | the binary64 specification `spec/math/f64.bend` itself against the machine's doubles, through a line-by-line mirror |
| `check_crypto_hash.py` | `src/crypto/subtle.bend`, SHA-512, SHA3-256 and the hashing facade (one-shot and incremental, random chunkings) against Python's `hashlib` and `==`, plus the FIPS vectors of `tests/crypto/{subtle,sha512,sha3,hash}/main.bend` |

The hash functions are fuzzed by `tests/crypto/fuzz.py` (random messages
against hashlib, pycryptodome and the official BLAKE3 C).

### Backend differential harness

`backend_diff.py` compares Bend with itself. The proofs are about the source;
the C and JavaScript backends are not verified. Each case is one invocation of
a driver on the same argv through three execution paths, and the outputs must
be identical:

| Path | Command |
|---|---|
| `run` | `bend driver.bend -- args` (check, then run in the bundled runtime) |
| `c` | `bend driver.bend -o bin`, then `bin --threads 1 -- args` |
| `js` | `bend driver.bend -o out.js`, then `node out.js -- args` |

```sh
python3 tools/backend_diff.py                     # every module, about 35 minutes at -j 4
python3 tools/backend_diff.py --quick             # about 4 minutes
python3 tools/backend_diff.py --only crypto       # a group (base, containers, math, crypto) or module names
python3 tools/backend_diff.py --only fixed --seed 7 --case 3 --show   # one case, with every path's output
python3 tools/backend_diff.py --list
```

No reference is involved, so functions without one are covered too. Inputs
are seeded (`--seed`, default 2026) random values mixed with values chosen to
provoke code generation bugs: 0, 1, 2^16 ± 1, 2^31 ± 1, 2^32 - 1, all-ones and
alternating words, Nats around 2^32 and up to the runtime's limit 2^48 - 1,
empty, one-element and large collections, byte lengths around every block
boundary, and a U32 local used several times and then converted to Nat (the
shape of bendlang/bend#1142). Where a function needs a valid input that only
the library can produce (a signature to verify, a ciphertext to open, a PHC
string), the native build produces it first and the harness then feeds it,
intact and damaged, to all three paths.

The drivers are the existing ones in `tests/` where they take their input
from argv, plus `tests/backend_diff/` (`codegen.bend`: the Base primitives
everything compiles down to; `hashes.bend`, `aead.bend`, `secp.bend`,
`lru.bend`). A disagreement prints the module, the seed, the case index, the
first differing line and a minimised argv (one token for the stateless
drivers, a shortened history for the stateful ones), and the exit status is 1.
`build/backend_diff/report.json` has every count. `validate.py` runs the full
harness as its `backend_diff` row.

Counted, but not failures: a case where every path stops with the same
runtime error (`all-fail`, the probes of the 2^48 Nat limit), a case where a
path overflows its machine stack and the others agree (`resource-limit`;
`--strict` fails on it), and the divergences recorded in
[docs/BACKEND_BUGS.md](../docs/BACKEND_BUGS.md) (`known`).

Full run on the server (Bend 2.0.34, seed 2026, `-j 4`, 48 cores shared,
2026-09-30): 7383 cases, 1 028 251 output lines compared across the three
paths, **0 disagreements**; 5 all-fail probes of the Nat limit, 1
resource-limit (the depth-100 000 probe), known divergences char-range 6,
f32-show-tie 5, nan-bits 3318 lines. 1954 s wall. `--quick` (126 cases,
23 884 lines): 147 s; with `--c-threads 4 --seed 11` it passes too.

| Module | Group | Covers | Cases | Lines compared | Seconds |
|---|---|---|---|---|---|
| `codegen` | base | Base primitives: U32, Nat, F32, String, Char, Array, List (the #1142 shapes, the 2^48 Nat limit); src/math/hash.bend, pow2.bend | 456 | 34714 | 56.0 |
| `stack` | containers | src/containers/stack.bend | 360 | 58691 | 50.3 |
| `queue` | containers | src/containers/queue.bend | 360 | 57007 | 54.6 |
| `simple_queue` | containers | src/containers/simple_queue.bend | 240 | 39993 | 42.2 |
| `deque` | containers | src/containers/deque.bend | 360 | 58186 | 50.1 |
| `dynamic_array` | containers | src/containers/dynamic_array.bend | 360 | 57443 | 59.1 |
| `binary_heap` | containers | src/containers/binary_heap.bend | 360 | 55306 | 51.9 |
| `priority_queue` | containers | src/containers/priority_queue.bend | 240 | 39242 | 33.6 |
| `bitset` | containers | src/containers/bitset.bend | 360 | 55290 | 44.4 |
| `bitlist` | containers | src/containers/bitlist.bend | 360 | 60460 | 41.0 |
| `doubly_linked_list` | containers | src/containers/doubly_linked_list.bend | 360 | 56693 | 48.7 |
| `dlist_iterator` | containers | src/containers/dlist_iterator.bend | 360 | 58382 | 43.8 |
| `intrusive_list` | containers | src/containers/intrusive_doubly_linked_list.bend, intrusive_links.bend | 117 | 41122 | 26.5 |
| `tree_map` | containers | src/containers/balanced_search_tree.bend | 360 | 73690 | 117.1 |
| `hash_table` | containers | src/containers/hash_table.bend, src/math/hash.bend | 360 | 60786 | 37.5 |
| `lru` | containers | src/containers/lru.bend | 450 | 72436 | 64.7 |
| `natural` | math | src/math/natural.bend | 31 | 6023 | 2.9 |
| `generic` | math | src/math/generic.bend, instances.bend, num.bend (U32, U64, F32, F64) | 144 | 21600 | 29.1 |
| `fixed` | math | src/math/fixed.bend, number.bend, u64.bend, w64.bend, pow2.bend | 56 | 13917 | 10.6 |
| `f64` | math | src/math/f64.bend (arithmetic, comparisons) | 77 | 15300 | 11.8 |
| `f64x` | math | src/math/f64.bend (rounding, conversions, remainders) | 75 | 15000 | 12.3 |
| `random` | math | src/math/random.bend, random/, src/crypto/random.bend | 360 | 50364 | 187.6 |
| `hashes` | crypto | subtle, SHA-256 (list, packed), SHA-512, SHA3-256, the incremental hash facade, Keccak-256, BLAKE2b/2s/3, HMAC, HKDF | 195 | 11523 | 131.2 |
| `aead` | crypto | aead.bend (ChaCha20-Poly1305, XChaCha20-Poly1305, AES-128-GCM, AES-256-GCM), chacha20, poly1305, the AES block cipher | 172 | 6873 | 97.4 |
| `argon2` | crypto | src/crypto/argon2/ | 91 | 1087 | 37.6 |
| `password` | crypto | src/crypto/password.bend | 86 | 1026 | 29.6 |
| `curve25519` | crypto | X25519, kex.bend, Ed25519, sign.bend | 261 | 3127 | 191.4 |
| `secp256k1` | crypto | secp256k1.bend (ECDSA, recover, ecrecover, Ethereum addresses, BIP-340) | 372 | 2970 | 258.2 |
| **total** | | | **7383** | **1 028 251** | **1954** (with the 3-minute build) |

## Changing a proof

1. Edit the `.src` (or the generator), regenerate the `.bend`.
2. Check the package: `python3 proofs/prove.py <package>` (or
   `bend proofs/containers/<package>/proof.bend`); success prints
   `ALL PROOFS CHECK`
3. Before committing, make sure every source still reproduces its committed
   `.bend` (the loop above leaves `git status` clean).
