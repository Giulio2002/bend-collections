> TreeMap update (2026-09-22): the production balanced search tree now uses
> dynamic-array metadata/payload slots and CLRS parent-linked red-black repair.
> The existing optimized C reference is unchanged. Native reads remain direct
> indexed block reads; the specialized return helper avoids boxing composite
> nodes. See `TREE_MAP.md` and the new TreeMap benchmark evidence. Historical
> recursive-tree claims below do not describe the current production tree.

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
  * `table : Map<&2, Maybe<&2, U32>>` (key -> `Some{slot}`, never `None`) —
    the native crit-bit trie of `Base`; the `Maybe` value type is what lets
    the proofs reuse the retained crit-bit Map theory of `reference/lru`
    (lookup after set/delete, crit-bit and populated preservation);
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
* **Laws**: proved for `fast.bend` against its independent model
  `spec/lru_fast.bend` (`proofs/lru_fast.bend`; laws `lru_fast_u32_*` and
  `lru_fast_string_*` in `END_TO_END.bend`): every operation's runtime result
  and observation, invariant preservation and model step, and arbitrary finite
  traces from the constructor, under the capacity condition (every capacity
  within 2^q, q <= 31). `tests/lru_fast/spec_diff.bend` also runs the runtime
  against that spec (6 x 300 operations, 0 mismatches).
* **Measurements** (supplemental: `python3 tools/lru_measure.py`, which runs
  `benchmarks/run.py`'s own `build_all`/`measure` on the PROPOSED rows of
  `benchmarks/experiments/lru_workloads.py`; report
  `build/performance/lru_experiment.json`; all rows checksum-verified):

  | row | bend ns | ref ns | ratio |
  |---|---:|---:|---:|
  | add small / medium / large | 210.83 / 396.67 / 1238 | 14.75 / 15.40 / 46.66 | 14.30x / 25.75x / 26.52x |
  | get small / medium / large | 155.71 / 361.67 / 1125 | 16.10 / 18.17 / 69.37 | 9.67x / 19.90x / 16.22x |
  | peek small / medium / large | 175.00 / 357.14 / 1173 | 16.82 / 14.45 / 38.72 | 10.40x / 24.72x / 30.29x |
  | contains small / medium / large | 154.38 / 354.29 / 1238 | 2.18 / 1.86 / 6.68 | 70.94x / 190.92x / 185.16x |
  | remove small / medium / large | 727.50 / 1545 / 3692 | 19.18 / 16.77 / 53.33 | 37.94x / 92.13x / 69.22x |
  | purge small / medium / large | 19583 / 1881250 / 198250000 | 420.50 / 30050 / 2562250 | 46.57x / 62.60x / 77.37x |
  | resize small / medium / large | 12917 / 1368750 / 94125000 | 319.71 / 31984 / 1447500 | 40.40x / 42.79x / 65.03x |
  | keys small / medium / large | 818.75 / 54250 / 404688 | 130.24 / 16455 / 126261 | 6.29x / 3.30x / 3.21x |
  | len small / medium / large | 1.33 / 1.27 / 1.33 | 3.39 / 3.95 / 3.71 | 0.39x / 0.32x / 0.36x |
  | new small / medium / large | 25.77 / 25.95 / 23.92 | 12.35 / 12.18 / 11.08 | 2.09x / 2.13x / 2.16x |
  | edge-empty new / add / get / peek / contains / remove / purge / resize / keys / len | 1.43 / 67.86 / 20.96 / 20.29 / 21.76 / 18.92 / 3.76 / 14.51 / 27.45 / 1.34 | 1.40 / 6.67 / 4.99 / 5.10 / 1.69 / 4.86 / 5.26 / 2.32 / 5.23 / 4.40 | 1.02x / 10.17x / 4.20x / 3.98x / 12.84x / 3.90x / 0.72x / 6.24x / 5.25x / 0.30x |

  (Re-measured 2026-09-21 after the table value type became
  `Maybe<&2, U32>`. The machine was shared with other jobs at load ~5, so
  both sides are ~1.5x slower in absolute terms than the earlier run; the
  ratios are within a few percent of it.)

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

## Iteration 0014: eager constructors, and what a constructor costs

The user rejected lazy initialization, so `graph` and
`doubly_linked_list` again allocate and initialise their storage inside `new`,
and `dynamic_array.clear` again rewrites the whole block (WORK_LOG.md records
the revert and the restored proofs). Honest constructor measurements taken
after the revert with `tools/dev/qrows.py` (ns per operation, best of three
alternating runs, quick tool - the gate's medians are in BENCHMARKS.md):

| row | Bend | C | ratio |
|---|---|---|---|
| `graph.new` small / medium / large / edge-empty | 11.1 / 11.3 / 11.2 / 11.3 | 1.74 / 1.74 / 1.08 / 1.87 | 6.4x / 6.5x / 10.4x / 6.0x |
| `doubly_linked_list.new` small / medium / large / edge-empty | 7.2 / 5.2 / 7.6 / 7.5 | 2.47 / 2.46 / 2.48 / 2.48 | 2.9x / 2.1x / 3.1x / 3.0x |
| `dynamic_array.clear` small / medium / large / edge-empty | 62 / 3500 / 209000 / 4.2 | 7.6 / 526 / 12996 / 2.2 | 8.1x / 6.7x / 16.1x / 1.9x |

What the two sides do:

* C `new`: one `arena_alloc` bump per table (graph: the id array and one
  adjacency block; DLL: one `Node`; union-find: one `Cell` array plus one
  `Member` per element), each about 0.3-0.5 ns, plus a few stores.
* Bend `new`: one `blk_new` per `Base.Array`, measured at about 3.5 ns each
  (iteration 0011 probe: a single depth-0 `Array.new` plus its release is
  4.6 ns including the ~1 ns driver baseline). `union_find` additionally
  allocates one cons cell per member list (a sealed `Con` is ~8.5 ns).
* `clear`: both sides are O(capacity) - the C reference memsets the whole slot
  array, Bend allocates a fresh all-None block. The gap is fill throughput:
  Bend's block fill writes one 8-byte Term per slot (~0.8 ns/slot) where
  `memset` is vectorised (~0.05 ns/slot).

So these rows are dominated by the allocator and the block fill, not by the
algorithm. Getting them under the limit needs FEWER allocations (one
interleaved record array, the layout the C references use) rather than
deferred ones; that migration is not done and is listed as remaining work.

## prefix_trie: the rows measure Base String, not the trie

A 10-character key is twenty heap cells in Bend (a `String` is a cons list of
`Chr`) and ten stack stores in C. A driver variant that only builds and folds
the key, with the trie call removed, still costs 87 ns (small) and 100 ns
(edge-empty) against the C reference's COMPLETE operation at 26.8 ns and
1.45 ns. `benchmarks/experiments/key/keycost.bend` measures the floor for the
key alone at 30 ns. No trie representation can bring those rows to 2.5x while
the key is built inside the timed region; docs/BENCHMARK_CHANGE_PROPOSAL.md
asks for additive rows with prepared keys on both sides.

The driver does remove the avoidable part of that cost: the old `char_at`
recomputed `U32.shrn(r, (16+2i) mod 30)` per character and Base's `U32.shrn`
walks its `Nat` shift one bit at a time, so each character paid about 25 shift
steps. The driver now carries the shifted word and advances it two bits per
character, exactly as `benchmarks/native/prefix_trie.c` does. Checksums are
unchanged: 28/28 rows identical to the C reference.

## Iteration 0015: what one shared algebraic node costs, measured directly

The claim that the two pointer-shaped structures (`balanced_search_tree` and
`prefix_trie`) are limited by reference counting rather than by their algorithm
is now backed by a pair of programs that differ ONLY in the representation they
walk. Both do the same data-dependent six-level descent, ten million times, one
sequential thread, and consume the result:

* `benchmarks/experiments/bstarena/descent.bend` walks a native indexed
  `Array<U32>` block: slot `2*cur + bit`, where `cur` is the value the previous
  load returned, so the addresses really chase. 112 ms for 60 M levels =
  **1.9 ns per level**.
* `benchmarks/experiments/bstarena/descent_adt.bend` walks a SHARED algebraic
  tree of the same six levels (the tree is `+`-reusable and handed back
  untouched, exactly as every read of `src/balanced_search_tree.bend` does).
  794 ms for 60 M levels = **13.2 ns per level**.

The ratio is about 7x, and it is the emitted `span_fade` / `term_drop` traffic:
opening a shared constructor retains all of its fields and then releases the
ones the walk does not follow, which is several read-modify-writes on scattered
heap words per level, against one indexed load.

Two consequences, both recorded honestly rather than acted on blindly:

* Migrating the tree and the trie onto an indexed arena IS worth doing on the
  merits of the representation rule, and it is the next representation step.
* It would NOT make those rows meet the 2.5x limit. `balanced_search_tree.min
  small` walks about six levels for 39.6 ns against a C walk of 1.0 ns; at
  1.9 ns per level plus the per-operation record traffic the arena version
  lands around 8-11x, because the C reference's six dependent L1 loads pipeline
  across loop iterations and cost the reference almost nothing. Claiming the
  migration would fix the gate would be wrong.

### `graph.vertices`: the block enumeration (landed in iteration 0015)

The pinned reference's `gr_vs` folds the vertex keys of its red-black set in
order and allocates NOTHING; the Bend side built a `List<U32>` and folded it,
so the row divided a list construction by a fold: 3.37x / 3.01x / 3.08x
(small / medium / large).

`src/graph.bend` now also exposes `vertices_block`, which copies the ascending
id window into slots `[0, n)` of a fresh `Array<U32>`; the driver folds that
block. Measured after the change (tools/dev/qrows.py, ns per operation, best
of three alternating runs, quick tool):

| row | Bend | C | ratio |
|---|---|---|---|
| `graph.vertices` small | 25.0 | 26.7 | 0.94x |
| `graph.vertices` medium | 480 | 498 | 0.96x |
| `graph.vertices` large | 3600 | 4187 | 0.86x |
| `graph.vertices` edge-empty | 3.20 | 3.26 | 0.98x |

`tools/dev/checksums.py graph` -> 40/40 rows identical to the pinned
reference; the pinned `benchmarks/native/graph.c` is byte-unchanged. The List
form `vertices` and its proofs are retained, and `proofs/graph/vblk.bend`
proves the block's window `[0, n)` IS the list `vertices` returns.

### Where the remaining over-limit rows come from

Classification of the 408 canonical rows that are over 2.5x, by cause (the
individual numbers are in BENCHMARKS.md, which is generated from the report):

| cause | rows | reducible? |
|---|---|---|
| `Base.String` key construction inside the timed region (`prefix_trie.*`) | ~20 | no, with the pinned rows; additive `prepared_keys` rows are proposed |
| shared algebraic node traffic (`balanced_search_tree.*`) | ~25 | partly (~3-4x), by the arena migration; not to 2.5x |
| allocator cost of a returned `List` (`*.to_list`) | ~7 | only where the C reference also folds without allocating: `graph.vertices` was fixed that way in iteration 0015 (3.0-3.4x -> 0.86-1.29x) and `bitset.to_list` is the one remaining such row. Where the C reference really builds a list (`queue.to_list` allocates a `Cell` per element) the comparison is already same-algorithm and the gap is the allocator: ~2 ns per cons cell against ~0.5 ns of an arena bump |
| block fill throughput (`dynamic_array.clear`) | 3 | no; `blk_new` is a scalar store loop, `memset` is vectorised |
| `new` rows whose C counterpart does no construction (`graph.new`, `doubly_linked_list.new`) | 8 | no; the pinned `gr_new`/`dl_new` only advance the value stream, so the row divides a real Bend constructor by a C no-op |
| per-operation record open/rebuild on an empty structure (`*.edge-empty` at 3-5x) | ~12 | marginally; ~3 ns of Bend runtime dispatch against ~1 ns in C |

This table is the current honest state of the performance criterion: it is NOT
met, the causes are measured, and the ones that are reducible are listed as
remaining work rather than claimed as done.
