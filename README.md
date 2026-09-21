> Latest development snapshot: native ring deque/queue proof and targeted test milestone. Full performance acceptance and semantic audit remain unfinished. Historical benchmark tables do not certify this changed runtime; see [SNAPSHOT_STATUS.md](SNAPSHOT_STATUS.md).

> Development snapshot: full acceptance is incomplete. LRU trace/uniqueness laws check at U32/String with capacities <=2^31, while the public constructor accepts larger capacities. Performance targets are not met. See [SNAPSHOT_STATUS.md](SNAPSHOT_STATUS.md).

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

Ten of them store their elements in native `Base.Array` blocks rather than in
node links: `dynamic_array` and `bitset` (indexed slots and packed words),
`deque` and `queue` (a window of a power-of-two block), `binary_heap` (a
packed array heap), `union_find` (three parallel arenas),
`fenwick_tree`/`segment_tree` (flat cells in a split-point layout),
`graph` (indexed vertex slots plus one sorted adjacency block per vertex) and
`doubly_linked_list` (three parallel arena blocks, with prev/next as arena
indices). The remaining two keep genuine links where the algorithm has them:
the red-black tree's children and the trie's children -- and `prefix_trie` is
the one structure whose migration is still outstanding.
`docs/ARCHITECTURE.md` has the representation table and
`docs/C_EQUIVALENCE.md` the comparison with each C reference.

Plus the retained LRU cache under `reference/lru` (an immutable, hash-pinned
snapshot) reused through `src/lru.bend`; nothing in it is re-implemented.
Base's native `Map`, `Set` and list-as-stack are reused as-is.

## Proofs

```sh
bend PROOF.bend          # the one root: every public law and everything under it
```

> **Current state:** `bend PROOF.bend` does NOT check. `graph` and
> `doubly_linked_list` were re-represented (indexed vertex slots plus
> adjacency blocks; parallel arena blocks) and their proofs are being rebuilt
> against the new representations -- see PROOF_STATUS.md and WORK_LOG.md for
> exactly what is proved today. The other ten structures' proofs check
> (`bend proofs/<id>.bend`).

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
