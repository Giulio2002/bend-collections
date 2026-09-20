> **Development snapshot:** implementation/proofs are incomplete and performance acceptance has not passed. See [current snapshot status and benchmark evidence](SNAPSHOT_STATUS.md).

# bend-dsa

A pure [Bend](https://github.com/HigherOrderCO/Bend) data-structure library with
machine-checked functional correctness proofs against independent mathematical
specifications.

Toolchain: Bend 2.0.16, pinned by sha256 in `inventory/toolchain.json`.

## What is here

Twelve structures (`inventory/structures.json`), each with a public API
(`src/<id>.bend`), an independent model (`spec/<id>.bend`) that never mentions
the implementation, and proofs (`proofs/<id>.bend`):

`dynamic_array`, `deque`, `queue`, `doubly_linked_list`, `binary_heap`,
`balanced_search_tree` (a red-black binary search tree), `bitset` (packed
words), `union_find`, `fenwick_tree`, `segment_tree`, `prefix_trie`, `graph`.

Seven of them store their elements in a native `Base.Array` rather than in
node links: `dynamic_array` and `bitset` (indexed slots and packed words),
`deque` and `queue` (a window of a power-of-two block), `union_find` (three
parallel arenas) and `fenwick_tree`/`segment_tree` (flat cells in a
split-point layout). The remaining five keep genuine links where the
algorithm has them - tree and trie children, doubly-linked prev/next - and
`doubly_linked_list`/`graph` use Base's own ordered map as their store.
`docs/ARCHITECTURE.md` has the representation table.

Plus the retained LRU cache under `reference/lru` (an immutable, hash-pinned
snapshot) reused through `src/lru.bend`; nothing in it is re-implemented.
Base's native `Map`, `Set` and list-as-stack are reused as-is.

## Proofs

```sh
bend PROOF.bend          # the one root: every public law and everything under it
```

For every structure and **every** inventoried operation, including every error
path, the proofs establish that the runtime step refines the specification step
and preserves the representation invariant from *any* invariant-satisfying
state, and that an *arbitrary finite* list of operations run from the real
constructor agrees with the specification run. No `@unsafe`, no holes, no
axioms, no finite enumeration standing in for a universal statement.

`balanced_search_tree` additionally proves the red-black invariants themselves:
black root, black empty leaves, no red-red parent/child edge, the same number
of black nodes on every root-to-leaf path, established by the constructor and
preserved by insertion *and* deletion including every rotation, recolouring and
the whole delete fixup path.

`graph` additionally proves model well-formedness — endpoint closure, the
self-loop policy and undirected symmetry — established by the constructor and
preserved by every operation, connected to the runtime invariant.

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
