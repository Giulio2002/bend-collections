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

## lru

* **C reference**: `benchmarks/native/lru.c` (NEW, rebuilt 2026-09-21 after
  the operator rejected the linear-recency version, which is quarantined at
  `docs/archive/lru-rejected-linear-reference.c.txt` and is NOT a baseline).
  The standard efficient LRU:
  * slot arena `key[] val[] dl[] prev[] next[]`; the recency order is an
    INTRUSIVE DOUBLY LINKED LIST through `prev/next` (head = oldest), so
    touch, detach, evict and remove are O(1); freed slots are reused from a
    free list chained through `next[]`;
  * lookup is an open-addressing hash table (linear probing, power-of-two
    size, load <= 1/2, backward-shift deletion, no tombstones) whose buckets
    hold `{key, slot}`, so a probe reads one cache line and never touches the
    arena;
  * arena and table grow geometrically; purge memsets the table and resets
    the arena cursor; resize evicts from the head.
  * Keys are `uint32_t` (the Bend key is the one-character String `Chr{65536 + i}`,
    the same 32-bit identity), so there is no key buffer at all: the
    rejected version's partially initialised `KEYMAX` buffer
    (`key_of` wrote a prefix, `memcpy`/`first_diff` read all of it) cannot
    recur. Validated by `tools/lru_diff.py`: the benchmark build and a
    `-fsanitize=address,undefined -fno-sanitize-recover=all` build agree with
    the Bend driver on all three region checksums for every selector over
    sizes 0-257, counts 0-200, two seeds and both region orders (1568 cases,
    0 mismatches, no sanitizer report).
* **Bend representation**: `src/lru/fast.bend` — the retained semantics
  over the SAME algorithmic layout, with the native `Map` kept for lookup as
  the operator requires:
  * `table : Map<&2, U32>` (encoded key -> slot) — the native patricia trie
    of `Base`;
  * `kys : Array<String>`, `ents : Array<Slot<V>>` (`Live{v}` or
    `Timed{v, deadline}`), `prevs/nexts : Array<U32>` — the intrusive doubly
    linked recency arena with a free list, O(1) touch/evict/remove;
  * the five 64-bit metrics as ten `U32` limbs in one `Array<U32>`
    (`to_metrics` rebuilds the retained `T.Metrics`); a 64-bit time is a
    `Stamp{lo, hi}` (`stamp_int`/`int_stamp` = `W.pack`/`W.unpack`); an
    immortal entry never consults the clock. The first version stored
    `Word(64n)` (a 64-node bit list) for times and counters and was 20x
    slower (peek 1.3 us); the representation change is what an optimized C
    implementation does (`int64_t`, `uint64_t`).
* **The lookup difference (documented, not hidden)**: C looks a key up with
  ONE hash probe; Bend's native `Map.get` descends the patricia trie
  (`Map.bit` = `Nat.divmod(pos, 33)` plus a character-bit extraction per
  level) and REBUILDS the path it walked (the map is a persistent value), and
  an insertion is `Map.get` + `Map.set`, an eviction adds `Map.del`. Measured
  floor in isolation (probe `benchmarks/experiments/map_get_floor.bend`, 1-character keys, 10^6 gets):
  `Map.get` alone costs 40 ns at 64 keys — four times the ENTIRE C `get`
  (10.4 ns) — and about 250 ns at 262144 keys. No arena change can remove
  this: with the native Map retained, the keyed `lru.*` rows cannot reach
  2.5x of a hash-table C reference. The non-lookup work (arena, recency,
  metrics) is at C shape.
* **Conformance to the retained cache**: `tests/lru_fast/main.bend` runs
  `fast.bend` and the retained cache (`src/lru/cache.bend`, the compilable
  copy of `reference/lru/src/cache.bend`) on eight seeded 3000-request
  sequences of add/get/peek/contains/remove/purge/keys/len/set_lifetime and
  clock advances (lifetimes 0, 5 ms, 20 ms; capacity 3; six keys) and
  compares every observation, the length and all five metrics after every
  request, plus constructor acceptance at capacities 0, 1, 3, 0xFFFFFFFF:
  0 mismatches. It found two real divergences of the first port, both
  fixed: `new(0xFFFFFFFF)` must be rejected (retained `new` is
  `new_with_size(cap, cap)`), and `keys` must first remove the oldest
  expired prefix (retained public `Keys`). Sensitivity: five planted bugs
  (peek touching, keys without expiry, eviction counted as removal, replace
  without touch, expiry ignored) are each detected on 8 of 8 seeds.
  `tools/validate.py` runs it. The benchmark drivers: `tools/lru_diff.py`
  (above); the retained behaviour
  (capacity eviction of the oldest, touch on get, no touch/no metric on
  peek/contains, removals/evictions/hits/misses/inserts counters, purge
  clears metrics, capacity 0 rejected) is exercised by both drivers and
  folded into every round's checksum (the drain folds all five metrics).
* **Laws**: NOT yet proved for `fast.bend` (PROOF_STATUS.md). The retained
  `reference/lru` proofs cover the retained list-recency cache only.
* **Measurements** (supplemental: `python3 tools/lru_measure.py`, which runs
  `benchmarks/run.py`'s own `build_all`/`measure` on the PROPOSED rows of
  `benchmarks/experiments/lru_workloads.py`; report
  `build/performance/lru_experiment.json`; all rows checksum-verified):

  | row | bend ns | ref ns | ratio |
  |---|---:|---:|---:|
  | add small / medium / large | 122.78 / 245.56 / 763.64 | 9.24 / 9.90 / 24.55 | 13.29x / 24.79x / 31.11x |
  | get small / medium / large | 96.82 / 222.22 / 784.38 | 10.39 / 11.74 / 41.24 | 9.32x / 18.93x / 19.02x |
  | peek small / medium / large | 94.58 / 215.00 / 696.88 | 9.77 / 9.76 / 24.81 | 9.68x / 22.04x / 28.09x |
  | contains small / medium / large | 95.83 / 217.00 / 753.12 | 1.41 / 1.27 / 4.38 | 67.93x / 170.46x / 172.14x |
  | remove (+add) small / medium / large | 458.33 / 1030.00 / 2300.00 | 12.41 / 11.44 / 31.47 | 36.92x / 90.03x / 73.07x |
  | purge (+refill) small / medium / large | 12250 / 1333333 / 139750000 | 253.72 / 21620.83 / 1738250 | 48.28x / 61.67x / 80.40x |
  | resize (+back) small / medium / large | 9000 / 1090625 / 69875000 | 209.17 / 21234.38 / 1081250 | 43.03x / 51.36x / 64.62x |
  | keys small / medium / large | 613.64 / 39125 / 350000 | 86.32 / 11113.38 / 90618.75 | 7.11x / 3.52x / 3.86x |
  | len small / medium / large | 1.01 / 1.01 / 1.04 | 2.93 / 2.91 / 2.92 | 0.35x / 0.35x / 0.36x |
  | new small / medium / large | 17.07 / 17.79 / 17.89 | 8.13 / 7.73 / 8.26 | 2.10x / 2.30x / 2.17x |
  | edge-empty new / add / get / peek / contains | 1.01 / 38.81 / 14.92 / 15.69 / 15.55 | 1.01 / 4.23 / 3.75 / 3.95 / 1.23 | 1.00x / 9.17x / 3.98x / 3.97x / 12.61x |
  | edge-empty remove / purge / resize / keys / len | 13.82 / 3.95 / 10.51 / 20.20 / 1.00 | 3.62 / 3.99 / 1.75 / 3.80 / 2.90 | 3.81x / 0.99x / 6.00x / 5.31x / 0.35x |

  `contains` is so far over because the C loop has no dependency from one
  probe to the next (the result folds a single bit), so the out-of-order
  core overlaps successive probes down to 1.3-4.4 ns; the Bend side pays the
  full `Map.get` each time. purge/resize rows are restoring pairs (the
  refill is identical work on both sides and is charged to the operation).

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
