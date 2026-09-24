# bend-collections

Collections for [Bend 2](https://bend-lang.com), written in stock Bend and
benchmarked against optimized C implementations of the same algorithms.

| Container | Module | Notes |
|---|---|---|
| Dynamic array | `src/containers/dynamic_array.bend` | packed storage, amortized push |
| Deque | `src/containers/deque.bend` | two-list deque |
| FIFO queue | `src/containers/queue.bend` | two-list queue |
| Stack | `src/containers/stack.bend` | |
| Simple / priority queue | `src/containers/{simple,priority}_queue.bend` | facades over queue and heap |
| Binary heap | `src/containers/binary_heap.bend` | packed-array min-heap, static comparator |
| Doubly linked list | `src/containers/doubly_linked_list.bend` | arena-backed, stable handles |
| List iterator | `src/containers/dlist_iterator.bend` | owning bidirectional iterator |
| Tree map | `src/containers/balanced_search_tree.bend` | indexed red-black tree |
| Bitset | `src/containers/bitset.bend` | packed words |
| Bit list | `src/containers/bitlist.bend` | growable packed bits, optional limit (SSZ `Bitlist[N]`) |
| Hash map | `src/containers/hash_table.bend` | String keys, Base.Map-style API |
| LRU cache | `src/containers/lru.bend` | String keys, lifetimes, 64-bit metrics |
| SHA-256 | `src/crypto/sha/sha256.bend` | FIPS 180-4, from [bend-sha256](https://github.com/Giulio2002/bend-sha256) |
| Keccak-256 | `src/crypto/keccak/keccak.bend` | Ethereum Keccak-256 (MIT), from [bend-keccak](https://github.com/Giulio2002/bend-keccak) |
| BLAKE2s | `src/crypto/blake/blake2s/blake2s.bend` | RFC 7693, 32-byte digest |
| BLAKE2b | `src/crypto/blake/blake2b/blake2b.bend` | RFC 7693, 64-byte digest |
| BLAKE3 | `src/crypto/blake/blake3/blake3.bend` | hash mode, 32-byte digest |
| Integer math | `src/math/natural.bend` | Python-style `math` integer functions, see below |

The hash map and the LRU follow Base's conventions: signatures are
quantity-polymorphic (`a, -V: Kind(a)`, as `Base.Map` uses), and reads that
copy a value out (`get`, `peek`) take `-V: Data` on the `&2` instance, like
`Map.get`.


## Integer math

`src/math/natural.bend` is the exact-integer part of a Python-style math
library, after the design reference's roadmap (numeric built-ins and the
`math` module's integer functions first), on Bend's natural numbers:

| Function | Python | Result |
|---|---|---|
| `gcd(a, b)`, `gcd_all(xs)` | `math.gcd` | greatest common divisor; `gcd_all([]) == 0` |
| `lcm(a, b)`, `lcm_all(xs)` | `math.lcm` | least common multiple; `lcm_all([]) == 1` |
| `isqrt(n)` | `math.isqrt` | `r*r <= n < (r+1)*(r+1)` (Heron's iteration) |
| `iroot(n, k)` | — | `r^k <= n < (r+1)^k`, `Domain` for `k == 0` |
| `ilog(n, b)` | — | `b^r <= n < b^(r+1)`, `Domain` for `n == 0` or `b < 2` |
| `factorial(n)`, `perm(n, k)`, `comb(n, k)` | `math.factorial/perm/comb` | `n!`, `n!/(n-k)!`, `C(n, k)`; 0 when `k > n` |
| `prod(xs)`, `sum(xs)` | `math.prod`, `sum` | `prod([]) == 1` |
| `pow_mod(b, e, m)` | `pow(b, e, m)` | `b^e mod m`, `ZeroDivision` for `m == 0` |
| `mod_inverse(a, m)` | `pow(a, -1, m)` | `a*x == 1 (mod m)`, `NotInvertible` when not coprime |
| `divmod(a, b)` | `divmod` | `QR{a // b, a % b}`, `ZeroDivision` for `b == 0` |
| `bit_length(n)` | `int.bit_length` | `2^(L-1) <= n < 2^L` |
| `clamp(x, lo, hi)` | — | `x` limited to `[lo, hi]`, `Domain` for `hi < lo` |

Errors are values (`MathError`: `ZeroDivision`, `Domain`, `NotInvertible`),
following the reference's error model. Every function is proved against
its specification in `proofs/math/natural/` (statement shapes follow Lean 4
Mathlib, the Why3 gallery and HACL*; each file cites its source), and
`tools/check_math.py` compares ~5000 random and edge-case calls with
CPython. Floating point (`math.sqrt`, `exp`, `sin`, ...), `cmath`,
`fractions`, `decimal`, `statistics` and `random` are not included: Bend
has no binary64 type (only `F32`, with no rounding guarantees to prove
against), and exact rationals need unbounded integers — Bend's native
backend stops at 2^48 - 1 per Nat, so results and intermediates of these
functions must stay below that at run time (the proofs are over all
naturals).

## Install

The library is published on the Bend hub. Import any module by its path in
the package:

```python
import 0x9ee2e9a299991dcc089fe22c7f3ceb5f/src/containers/hash_table.bend as HashMap
import 0x9ee2e9a299991dcc089fe22c7f3ceb5f/src/crypto/sha/sha256.bend as SHA256
```

The hash names the exact content (every file is checked against it when
fetched), so an import never changes under you; each release lists its hash.
`main.bend` imports every public module and is what gets published
(`bend main.bend --publish`).

## Layout

```
src/containers/   the collections, their internals (internal/) and API types (types/)
src/math/         integer math (natural.bend), 64-bit words, hashing, powers of two
src/crypto/       SHA-256 (sha/), Keccak-256 (keccak/), BLAKE2s, BLAKE2b and BLAKE3 (blake/)
proofs/           one proof package per src package, mirroring src/:
  containers/<pkg>/   spec.bend (the independent specification), the lemmas,
                      the .src sources they expand from, and proof.bend (the
                      package's entry point: its theorems)
  math/<pkg>/         the same for src/math (math/proof.bend gates them all)
  crypto/<pkg>/       the same for src/crypto: sha/ proves SHA-256 equal to an
                      executable FIPS 180-4 specification for every input,
                      keccak/ the packed API equal to an independent sponge
                      specification (padding, absorption, rejection, all words)
  lib/                proof library shared by the packages (logic, Nat, lists,
                      U32 words, arrays, order laws)
  PROOF.bend          the whole library; END_TO_END.bend the public laws
  prove.py            checks every proof
tests/            native test drivers, one per container; oracles in tests/support/
benchmarks/       bend/ and native/ (C) drivers, workload table, runner
tools/            proof generators (mac.py expands the .src proof sources),
                  validation and differential tests: see tools/README.md
```

## Requirements

Bend 2.0.25 (pinned in `tools/toolchain.json`), clang and Python 3.

## Test

```sh
bend tests/<container>/main.bend    # each container's test driver
bend tests/math/natural.bend -o build/math/natural && python3 tools/check_math.py   # math vs CPython
```

## Benchmark

```sh
python3 benchmarks/bench.py --build
python3 benchmarks/full_sweep.py           # calibrated, every size
python3 benchmarks/natural.py --report build/bench/math.json   # src/math/natural.bend
```

Every container and both hashes run the same algorithm in Bend (native C
backend) and in C, with identical inputs and a checksum that must match.
Results and the differences to C: [BENCHMARK.md](BENCHMARK.md).
