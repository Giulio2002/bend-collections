# bend-collections

Collections for [Bend 2](https://bend-lang.com), written in stock Bend and
benchmarked against optimized C implementations of the same algorithms.

| Container | Module | Notes |
|---|---|---|
| Dynamic array | `src/containers/dynamic_array.bend` | packed storage, amortized push |
| Deque | `src/containers/deque.bend` | two-list deque |
| FIFO queue | `src/containers/queue.bend` | two-list queue |
| Stack | `src/containers/stack.bend` | |
| LIFO / simple / priority queue | `src/containers/{lifo,simple,priority}_queue.bend` | facades over stack, queue and heap |
| Binary heap | `src/containers/binary_heap.bend` | packed-array min-heap, static comparator |
| Doubly linked list | `src/containers/doubly_linked_list.bend` | arena-backed, stable handles |
| List iterator | `src/containers/dlist_iterator.bend` | owning bidirectional iterator |
| Tree map | `src/containers/balanced_search_tree.bend` | indexed red-black tree |
| Bitset | `src/containers/bitset.bend` | packed words |
| Hash map | `src/containers/hash_table.bend` | String keys, Base.Map-style API |
| LRU cache | `src/containers/lru.bend` | String keys, lifetimes, 64-bit metrics |
| SHA-256 | `src/crypto/sha/sha256.bend` | FIPS 180-4, from [bend-sha256](https://github.com/Giulio2002/bend-sha256) |
| Keccak-256 | `src/crypto/keccak/keccak.bend` | Ethereum Keccak-256 (MIT), from [bend-keccak](https://github.com/Giulio2002/bend-keccak) |

The hash map and the LRU follow Base's conventions: signatures are
quantity-polymorphic (`a, -V: Kind(a)`, as `Base.Map` uses), and reads that
copy a value out (`get`, `peek`) take `-V: Data` on the `&2` instance, like
`Map.get`.

## Layout

```
src/containers/   the collections, their internals (internal/) and API types (types/)
src/math/         64-bit words, hashing, powers of two
src/crypto/       SHA-256 (sha/) and Keccak-256 (keccak/)
proofs/           one proof package per src package, mirroring src/:
  containers/<pkg>/   spec.bend (the independent specification), the lemmas,
                      the .src sources they expand from, and proof.bend (the
                      package's entry point: its theorems)
  math/<pkg>/         the same for src/math (math/proof.bend gates all three)
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
```

## Requirements

Bend 2.0.25 and clang.

## Test

```sh
bend tests/<container>/main.bend    # each container's test driver
```

## Benchmark

```sh
python3 benchmarks/bench.py --build
python3 benchmarks/full_sweep.py           # calibrated, every size
```

Every container and both hashes run the same algorithm in Bend (native C
backend) and in C, with identical inputs and a checksum that must match.
Results and the differences to C: [BENCHMARK.md](BENCHMARK.md).
