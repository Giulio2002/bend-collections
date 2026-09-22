# bend-collections

Stock Bend 2.0.16 collections with optimized C references, differential tests,
and formal proofs in progress. **The full `PROOF.bend` gate currently fails;
passing component gates do not establish whole-library correctness.**

Current collection inventory: dynamic array, deque, FIFO queue, stack,
arena-backed doubly linked list, binary min-heap, red-black search tree,
bitset, union-find, segment tree, LRU, LifoQueue, SimpleQueue, PriorityQueue.
Fenwick tree, graph and Trie have been removed. No Counter is included.

The three queue facades reuse the existing implementations:

| Module | Ordering | Storage | Public operations |
|---|---|---|---|
| `src/lifo_queue.bend` | Last in, first out | Stack | `new`, `put`, `get`, `peek`, `qsize`, `to_list` |
| `src/simple_queue.bend` | First in, first out | Two-list queue | `new`, `put`, `get`, `peek`, `qsize`, `to_list` |
| `src/priority_queue.bend` | Minimum comparator value first | Packed-array binary heap | `new`, `put`, `get`, `peek`, `qsize`, `from_list`, `to_sorted_list` |

These APIs are single-threaded and nonblocking, with no capacity limit or
thread/task synchronization. Empty `get`/`peek` returns the underlying typed
error. Elements are generic `Data`; priority ordering uses a static comparator.
Equal priorities have no stable insertion-order guarantee. The returned state
must be threaded into subsequent calls. The underlying state types are reused.
C benchmarks include the same reference implementations, without duplicated or
modified algorithms. Queue facades are measured separately from their base APIs.

Build once, then obtain a quick rundown with a 60-second wall-clock budget:

```sh
python3 benchmarks/bench.py --build
python3 benchmarks/bench.py --quick
```

Quick mode samples one nonempty size per operation and reports estimates,
low-resolution rows and timeouts explicitly. It is not the 2.5x acceptance gate.
Build time is separate. Full calibrated measurements remain in
`benchmarks/full_sweep.py`.

`QUEUE_ADAPTER_PROOF.bend` checks U32 API delegation for put/get/qsize over
arbitrary underlying states. `STACK_COMPONENT_PROOF.bend` checks stack step
refinement for U32/String. Two-list component proofs and randomized tests are
also retained. Full queue/deque trace and generational arena-DLL proofs remain
unfinished. No new axioms or unsafe declarations were introduced; checker
unsafe counts include existing dependencies.

Plus the retained LRU cache under `reference/lru` (an immutable, hash-pinned
snapshot) reused through `src/lru.bend`; nothing in it is re-implemented.
Base's native `Map`, `Set` and list-as-stack are reused as-is.

## Proofs

```sh
bend PROOF.bend          # the one root: every public law and everything under it
```

> **Current state:** `bend PROOF.bend` does NOT check. The two-list queue
> and deque have checked component laws, but their previous ring-buffer trace
> proofs need replacement. See `PROOF_STATUS.md`; do not interpret historical
> acceptance or proofs for earlier representations as current coverage.

The intended proof contract is universal public-operation refinement and
invariant preservation against independent specifications, including errors
and arbitrary finite traces. This migration has not yet re-established that
whole contract.

`balanced_search_tree` additionally proves the red-black invariants themselves:
black root, black empty leaves, no red-red parent/child edge, the same number
of black nodes on every root-to-leaf path, established by the constructor and
preserved by insertion *and* deletion including every rotation, recolouring and
the whole delete fixup path.

`graph` additionally proves model well-formedness — endpoint closure, the
self-loop policy and undirected symmetry — established by the constructor and
preserved by every operation. That development is about the SPEC and survives
the representation change; its connection to the new runtime invariant is
part of the rebuild.

Details: `PROOF_STATUS.md`, `docs/PROOF_MAP.md`.

## Validation

```sh
python3 tools/validate.py --report build/validation.json
python3 automation/acceptance.py          # the frozen mechanical gate
```

Native binaries of `tests/<id>/main.bend` are compared line by line against
independent Python oracles over functional, boundary, differential, structural
and mutation scenarios. See `docs/VALIDATION.md`; the last run is archived in
`VALIDATION.json`.

## Performance

```sh
python3 automation/performance_gate.py
```

Bend's native C backend against optimized same-algorithm C references in
`benchmarks/native/`. **The contract (every workload within 2.5x of C) is not met** —
the measured ratios and the reasons are in `BENCHMARKS.md`.

## Layout

`docs/ORGANIZATION.md` (conventions), `docs/ARCHITECTURE.md` (module and
dependency map), `docs/API.md` (API index), `docs/PROOF_MAP.md`,
`docs/VALIDATION.md`, `WORK_LOG.md` (chronological engineering log, including
the toolchain defects found and their reproducers under
`tests/runtime_defects/`).
