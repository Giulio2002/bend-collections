# bend-dsa

> **Two-list migration (2026-09-22):** Queue and deque now use the user's
> two-list design, with matching C implementations. The standalone DLL is
> retired. Runtime/oracle checks and new component proofs pass; **full trace
> proofs are still being migrated and `PROOF.bend` does not pass**.
> See [the migration report](docs/TWO_LIST_MIGRATION.md) for scope, tests,
> limitations and reproducible commands.

A pure [Bend](https://github.com/HigherOrderCO/Bend) data-structure library with
machine-checked functional correctness proofs against independent mathematical
specifications.

Toolchain: Bend 2.0.16, pinned by sha256 in `inventory/toolchain.json`.

## What is here

Eleven structures (`inventory/structures.json`), each with a public API
(`src/<id>.bend`), an independent model (`spec/<id>.bend`) that never mentions
the implementation, and proofs (`proofs/<id>.bend`):

`dynamic_array`, `deque`, `queue`, `binary_heap`,
`balanced_search_tree` (a red-black binary search tree), `bitset` (packed
words), `union_find`, `fenwick_tree`, `segment_tree`, `prefix_trie`, `graph`.

Queue and deque use ordinary singly linked lists where their algorithms need
links. Their stored order is front followed by reversed back. The other
structures retain their current representations; the standalone doubly linked
list is no longer in scope. Historical representation tables are superseded
for queue/deque by `docs/TWO_LIST_MIGRATION.md`.
`docs/ARCHITECTURE.md` has the representation table and
`docs/C_EQUIVALENCE.md` the comparison with each C reference.

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
