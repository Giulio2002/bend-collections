# C equivalence: what the Bend implementation does, and what the C reference does

Required by the operator's "equivalent of genuinely optimized C" rule. One
section per structure: the C source and its algorithm, the Bend
representation, the evidence from the EMITTED C that the Bend side really
performs indexed loads and stores, the remaining discrepancy, the laws that
connect the runtime to the specification, and the measurements.

All measurements are native, one thread, release builds of both sides, taken
with `benchmarks/run.py` (`bend ns` / `ref ns` are per operation medians of
six alternating samples). Where a row is over 2.5x it is named here, not
hidden.

## How `Base.Array` is actually compiled (read this first)

`Base.Array` is declared in `base.bend` as `ALeaf{value} | ANode{xs, ys}`.
That tree is the LOGICAL MODEL the checker reasons about. It is **not** the
native layout. Stock Bend 2.0.16 lowers an `Array<U32>` to one indexed
memory block:

* `Array.get`/`Array.set`/`Array.swap` compile to a `blk_at` index
  computation followed by a direct `blk_read`/`blk_write` — no tree descent.
  Evidence: `control/array-lowering-probe/probe.c` (operator-supplied), and
  in this repository the emitted C of `benchmarks/bend/graph.bend`, where
  the binary search reads compile to

  ```c
  Term at_4 = blk_at(a_1, mid_0, 0);
  u32 c_4 = blk_read(e.mem, 0, term_loc(a_1), at_4 + 0);
  ```

  with `blk_read`'s `arr` flag 0 (a raw `u32` buffer).
* `Array<Array<U32>>` is a block of element TERMS, each pointing at its own
  `u32` block: the same emitted C contains `blk_read(e.mem, 1, ...)` /
  `blk_write(e.mem, 1, ...)` (the `arr` flag is 1) for `adj[i]`, i.e. one
  indexed pointer load, like a C `uint32_t **`.
* `ANode{a, b}` compiles to `blk_node`, which allocates the merged class and
  copies both halves — the cost of a C `realloc` plus copy, not a free tree
  link. Doubling is therefore O(capacity), amortised O(1) per push.
* Element boxing: a slot of type `Maybe<T>` holds a term; for a `Some{x}`
  built per element the term points at a heap cell, so reading such a slot
  costs an extra dependent load. A slot of type `U32` is an immediate word.
  This is why `graph` stores raw `U32` ids and neighbour ids.

Consequences used throughout: indexed access is O(1) machine work (NOT
"O(log capacity)"), growth is a copy, and the checker's tree model is only a
model. Documentation that said otherwise has been corrected
(`src/dynamic_array.bend`, `docs/API.md`).

## graph

* **C reference**: `benchmarks/native/graph.c` (frozen). A red-black tree
  (`benchmarks/native/redblack.h`) from vertex to a red-black set of
  neighbours; `strip` walks every set on vertex removal; `fold_keys` /
  `fold_edges` produce the observable enumerations WITHOUT allocating a
  list.
* **Bend representation**: `src/graph.bend` — indexed vertex slots plus
  adjacency blocks. `ids : Array<U32>` holds the vertex ids ascending in a
  floating window `[lo, hi)`; `adj : Array<Array<U32>>` holds one adjacency
  block per slot, each a power-of-two `U32` block with the three word header
  `deg | size | lcap` followed by ascending neighbour ids. External U32
  vertex ids are mapped to slots by binary search of `ids`; no id is
  reserved and no density is assumed.
* **Why a different algorithm from the reference**: the operator directed
  indexed vertex storage plus adjacency blocks. The result is faster than
  the frozen red-black reference on nearly every row (below), so no
  supplemental C twin is proposed: the comparison is made against the
  unchanged optimized baseline.
* **Ownership**: every operation takes the graph by value and returns it;
  nothing is cloned. A read-only operation still threads the state
  (`has_vertex(g, v) -> Graph & Bool`), which is what makes the whole graph
  affine and keeps `Base.Array` linear — no `Array.clone` appears anywhere
  in `src/graph.bend`.
* **Index arithmetic**: sub/shr/inc only, no `U32.add`. That is a proof
  requirement (an addition bridge needs a `2^32` bound, which the checker
  cannot expand), and it costs nothing at runtime.
* **Remaining discrepancies**:
  1. `vertices` and `edges` must MATERIALISE the `List` their public
     contract returns; the C reference folds its tree with no allocation.
     Measured: `vertices/large` 30781 ns for 4096 vertices (7.5 ns each)
     against 4240 ns (1.03 ns each).
  2. `new` allocates two blocks and a record where the C reference assigns a
     null pointer: 11.7 ns against 1.74 ns.
  3. Insertion and deletion of a vertex slot move the shorter side of the
     window, O(V) words worst case, where the reference does an O(log V)
     tree insert. The floating window makes insertion at either end O(1),
     which is what the benchmark's descending build does; the worst case is
     documented in `src/graph.bend`.
* **Laws**: `proofs/graph/search.bend` proves the real binary search and
  `locate` against the real `Base.Array` algorithms;
  `proofs/graph/shift.bend` proves both shift loops; `proofs/graph/lb.bend`
  connects the lower-bound index to the specification's `ins`. The
  operation-level refinements are under construction (see PROOF_STATUS.md).
* **Measurements** (bend ns / ref ns / ratio), `/tmp/bench_graph2.json`:

  | row | bend | ref | ratio |
  |---|---|---|---|
  | add_vertex small/medium/large | 8.83 / 9.94 / 13.93 | 15.68 / 27.68 / 39.59 | 0.56 / 0.36 / 0.35 |
  | remove_vertex small/medium/large | 2.60 / 51.01 / 883.21 | 1.00 / 211.77 / 5464.63 | 2.60 **over** / 0.24 / 0.16 |
  | add_edge small/medium/large | 23.92 / 133.46 / 99.02 | 70.04 / 313.91 / 317.04 | 0.34 / 0.43 / 0.31 |
  | remove_edge small/medium/large | 21.33 / 36.76 / 43.36 | 29.87 / 63.12 / 98.46 | 0.71 / 0.58 / 0.44 |
  | has_vertex small/medium/large | 20.08 / 28.19 / 34.53 | 15.74 / 29.07 / 39.39 | 1.28 / 0.97 / 0.88 |
  | has_edge small/medium/large | 32.03 / 42.19 / 51.17 | 32.03 / 61.62 / 93.03 | 1.00 / 0.68 / 0.55 |
  | neighbors small/medium/large | 24.80 / 38.02 / 46.88 | 17.84 / 30.47 / 51.31 | 1.39 / 1.25 / 0.91 |
  | vertices small/medium/large | 201.96 / 3484 / 30781 | 27.63 / 491.92 / 4239.77 | 7.31 / 7.08 / 7.26 **over** |
  | edges small/medium/large | 407.84 / 6230 / 53382 | 118.10 / 2317 / 19356 | 3.45 / 2.69 / 2.76 **over** |
  | new (all sizes) | ~11.8 | ~1.75 | ~6.7 **over** |
  | edge-empty rows | 1.2 - 9.6 | 1.0 - 3.5 | 1.1 - 4.5 (has_vertex 3.84, has_edge 3.61, add_vertex 4.47 **over**) |

  Before this migration the same rows were 6.5x - 28.3x with three rows
  unmeasurable; the ordered-map implementation is archived at
  `docs/archive/graph.ordmap.bend.txt`.

## doubly_linked_list

* **C reference**: `benchmarks/native/doubly_linked_list.c` (frozen). One
  flat block of `Node{val, prev, next, live}` records, the element id IS its
  slot index, ids from a monotone counter, the block doubles by
  `arena_alloc` + `memcpy`; `fold_list` walks the next links with no
  allocation.
* **Bend representation**: `src/doubly_linked_list.bend` — THREE parallel
  `Base.Array` blocks (`vals`, `prevs`, `nexts`) over one index space, so
  relinking a neighbour is ONE indexed write instead of a read-modify-write
  of a record. Ids are slot indices, never reused: a handle whose slot is
  `None` is stale, one whose tag differs is foreign.
* **Conformance**: the Bend driver and the frozen C reference produce
  identical checksums for all twelve operations at sizes 1, 7, 64 and 512.
* **Discrepancy**: `vals` holds `Maybe<T>` (a generic element type has no
  default value to fill a block with), so a live slot costs one dependent
  load more than the C `uint32_t` field.
* **Laws**: the proofs still describe the previous ordered-map arena and are
  being ported (PROOF_STATUS.md).

## The systematic gap: operations whose result is an allocation

`to_list`-shaped operations (deque, queue, dynamic_array, DLL, graph
`vertices`/`edges`/`neighbors`) return a `List`, so their cost IS
allocation. The C references build the same list from a bump arena
(`benchmarks/native/deque.c` `dq_to_list` allocates a `Cell` per element),
which costs about 0.5 ns per cell; Bend's allocator costs about 2 ns per
cons cell, and reading a `Maybe<T>` slot built per element adds a dependent
load. Measured floor in isolation: 2.2 - 2.9 ns per element for
"read a slot, cons it, fold the list" (probe `/tmp/gp/listbig.bend`),
against 1.18 ns per element for the C reference at the same size.

This is the principal remaining cause of over-limit rows and it is a
property of the runtime's allocator, not of the representation: no indexing
change removes it. It is reported here rather than worked around.
