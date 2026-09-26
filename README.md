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
| SHA-256 (packed) | `src/crypto/sha/packed/sha256.bend` | the same hash over a packed `Array<U32>` and a byte length, no list on the path; laws in `proofs/crypto/sha/packed/laws.bend` |
| Keccak-256 | `src/crypto/keccak/keccak.bend` | Ethereum Keccak-256 (MIT), from [bend-keccak](https://github.com/Giulio2002/bend-keccak) |
| BLAKE2s | `src/crypto/blake/blake2s/blake2s.bend` | RFC 7693, 32-byte digest |
| BLAKE2b | `src/crypto/blake/blake2b/blake2b.bend` | RFC 7693, 64-byte digest |
| BLAKE3 | `src/crypto/blake/blake3/blake3.bend` | hash mode, 32-byte digest |
| Integer math | `src/math/natural.bend` | Python-style `math` integer functions, see below |
| Math per type | `src/math/generic.bend`, `src/math/f64.bend` | the same functions for U32, U64, F32 and a software F64, see below |

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
following the reference's error model. The contract is
`spec/math/natural.bend`: one `<Function>.<clause>` proposition per
guarantee (`Gcd.greatest`, `Isqrt.lt_succ`, `PowMod.zero_modulus`, ...;
divisibility is `dvd(d, a)`, a quotient with its equation), and
`proofs/math/natural/proof.bend` proves every clause under its name
(statement shapes follow Lean 4 Mathlib, the Why3 gallery and HACL*; each
file cites its source; coverage in `docs/MATH_CONTRACTS.md`), and
`tools/check_math.py` compares ~5000 random and edge-case calls with
CPython. Elementary float functions (`exp`, `sin`, ...), `cmath`,
`fractions`, `decimal`, `statistics` and `random` are not included:
exact rationals need unbounded integers, and Bend's native backend stops at
2^48 - 1 per Nat, so results and intermediates of these functions must stay
below that at run time (the proofs are over all naturals). The same
functions for U32, U64, F32 and a software binary64 follow below.

## Math per type: U32, U64, F32, F64

`src/math/generic.bend` writes the functions above once, as templates over a
numeric interface (`src/math/num.bend`): a type takes part through two
functions passed as templates, `~op: Op<T> -> T` (its arithmetic, one
constructor per operation) and `~test: Test<T> -> Bool` (comparisons and
overflow tests). Templates are substituted at compile time and the match on
the operation's constructor is resolved there, so each call compiles to the
instance's native code:

```python
import ./src/math/generic.bend as G
import ./src/math/instances.bend as I
import ./src/math/f64.bend as F64
import ./src/math/u64.bend as W

G.gcd(~U32, ~I.u32_op, ~I.u32_is, 12, 18)          # 6
G.comb(~W.U64, ~I.u64_op, ~I.u64_is, n, k)         # Done{C(n, k)} or Fail{Overflow}
G.clamp(~F32, ~I.f32_op, ~I.f32_is, x, lo, hi)
G.pow(~F64.F64, ~F64.f64_op, ~F64.f64_is, x, 10n)
```

| Instance | Type | Functions |
|---|---|---|
| `I.u32_op`, `I.u32_is` | Base `U32` | all of them |
| `I.u64_op`, `I.u64_is` | `src/math/u64.bend`'s two-word `U64` (fast arithmetic in `src/math/w64.bend`) | all of them |
| `I.f32_op`, `I.f32_is` | Base `F32` | `min max clamp abs sign sum prod pow` |
| `F64.f64_op`, `F64.f64_is` | `src/math/f64.bend`'s software binary64 | `min max clamp abs sign sum prod pow` |

The integer functions (`gcd lcm gcd_all lcm_all isqrt iroot ilog factorial
perm comb pow_mod mod_inverse divmod bit_length`) need an unsigned integer
instance; the ordered ones (`min max clamp abs sign sum prod pow`) any
instance. Fixed widths are checked: a result (or a partial product of `sum`,
`prod`, `lcm_all`) that does not fit is `Fail{Overflow}`, never a wrapped
value (the design reference's rule for fixed-width integers). `comb` reduces
by a gcd at every step and `pow_mod` / `mod_inverse` multiply mod m without
overflow, so they fail only when the true result does not fit. `isqrt` is
the instance's own: an F32 square-root estimate corrected exactly (U32), plus
one Newton step on 64 bits (U64).

`src/math/w64.bend` is the U64 arithmetic: only native `U32` operations and
`Nat` values below 2^48 (the runtime's bound), with 64/64 division by a
normalized 32-bit quotient estimate (at most two over, Knuth's Theorem B)
and a 128-bit product for `mulmod`.

`src/math/f64.bend` is IEEE-754 binary64 in software on two `U32` words
(Bend 2 has only `F32`): Berkeley SoftFloat 3e's algorithms (`addMags`,
`subMags`, `f64_mul`, `roundPackToF64`, `normRoundPackToF64`) on 64-bit
significands, exact long division by 32-bit quotient digits and an integer
square root with one Newton step, each rounded once to nearest-even, with
subnormals, signed zeros, infinities and NaN as IEEE 754; `lt le eq`,
`neg abs copysign`, the classification predicates and `of_nat`.

These instances are stated and tested, and mostly not proved (the Nat
functions above are the proved reference; at U32, `abs`, `min`, `max`,
`sign` and `clamp` are proved in `proofs/math/typed/u32.bend`). Their contracts are in `spec/math/`:
`generic.bend` relates every typed function to the proved Nat one
(`Gcd.agrees`, `Comb.checked`: the Nat result, or `Overflow` exactly when it
needs more than the width) and states the float ones through the type's
IEEE operations (`FSum.fold`, `FPow.binary`); `instances.bend` states what
each instance operation computes; `w64.bend` the 64-bit arithmetic;
`f64.bend` is an executable binary64 reference in Flocq's style (the exact
result of each operation, rounded once to nearest-even). The evidence:
`tools/check_generic.py` compares every function on every type with Python
(U32/U64 with overflow detection, F32 through numpy `float32`, F64 through
Python floats), naming the clause of each case; `tools/check_f64.py`
compares the software binary64 with the machine's doubles on random bit
patterns of every class (zeros, subnormals, normals, infinities, NaN,
cancellations, ties); `tools/check_f64_spec.py` tests `spec/math/f64.bend`
itself against the machine's doubles through a line-by-line mirror; and
`proofs/math/typed/examples.bend` has the proof checker evaluate the integer
clauses and instance laws at concrete U32 inputs. All run in
`tools/validate.py`; `docs/MATH_CONTRACTS.md` has the function-by-type
matrix.

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
src/math/         integer math (natural.bend), the same per type (num, generic, instances),
                  software binary64 (f64), 64-bit words (u64, w64), hashing, powers of two
src/crypto/       SHA-256 (sha/), Keccak-256 (keccak/), BLAKE2s, BLAKE2b and BLAKE3 (blake/)
spec/             the specifications, mirroring src/: what each module does,
                  independent of how
  containers/<pkg>.bend  the abstract model and its contract: every SPARK
                      formal-container Post clause as a `<Subprogram>.<clause>`
                      proposition (docs/SPARK_CONTRACTS.md); a spec spanning
                      several files is a directory with a main.bend
  crypto/             FIPS 180-4 SHA-256, the Keccak sponge, RFC 7693 BLAKE2,
                      BLAKE3
  math/<module>.bend  each src/math module's contract as `<Function>.<clause>`
                      propositions (docs/MATH_CONTRACTS.md): proved for
                      natural, u64, hash and pow2; stated and tested for the
                      typed versions (generic, instances, w64, f64)
  lib/                shared model definitions (lists, the SPARK sequence
                      predicates, order laws, U32 sequences, the 64-bit word
                      model)
proofs/           only proofs: one package per src package, mirroring src/,
                  each importing its spec from spec/:
  containers/<pkg>/   the lemmas, the .src sources they expand from, and
                      proof.bend (the package's entry point: the refinement
                      theorems and the proof of every contract clause)
  math/<pkg>/         the same for src/math: natural/proof.bend proves every
                      clause of spec/math/natural.bend, math/proof.bend those
                      of u64, hash and pow2; typed/examples.bend checks the
                      typed clauses at concrete U32 inputs
  crypto/<pkg>/       the same for src/crypto: sha/ proves SHA-256 equal to its
                      executable FIPS 180-4 specification for every input,
                      keccak/ the packed API equal to the independent sponge
                      specification (padding, absorption, rejection, all words)
  lib/                proof library shared by the packages (logic, Nat, lists,
                      U32 words, arrays, order laws)
  PROOF.bend          the whole library; END_TO_END.bend the public laws
  prove.py            checks every proof and every spec
tests/            native test drivers, one per container; oracles in tests/support/
benchmarks/       bend/ and native/ (C) drivers, workload table, runner
tools/            proof generators (mac.py expands the .src proof sources),
                  validation and differential tests: see tools/README.md
```

## Requirements

Bend 2.0.28 (pinned in `tools/toolchain.json`), clang and Python 3.

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
