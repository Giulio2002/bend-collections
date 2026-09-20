# Benchmarks

Bend's **native C backend**, one sequential worker thread, against **optimized
same-algorithm C references** in `benchmarks/native/`, built `-O3 -march=native`
on the same machine and run alternately.

> `native_bench/` at the repository root is a **stale leftover** from an older
> (2-3 tree) reference set. Nothing builds or reads it. It is outside the
> worker's editable scope, and deleting it counts as an out-of-scope change, so
> it cannot be removed from here; `benchmarks/run.py` still hashes it into
> `source_sha256` only because `automation/performance_gate.py` hashes every
> folder in that list which exists. The live references are
> `benchmarks/native/`.

Reproduce (this exact document is rendered from the report the runner writes,
so it cannot disagree with it):

```sh
python3 benchmarks/run.py --report build/performance/report.json
python3 tools/bench_report.py                 # regenerates BENCHMARKS.md
python3 automation/performance_gate.py        # builds, runs and validates
```

## How a row is measured

`benchmarks/bend/<id>.bend` and `benchmarks/native/<id>.c` take the identical argv
`[op, size, count, reps, seed, order]`, draw every operation argument from the
identical LCG (`s*1664525 + 1013904223`), and fold every result into the
identical checksum (`c*31 + v`). One *round* is

```
build a structure of `size`  ->  settle it  ->  run the measured operation
k times  ->  destroy it
```

and each program times **three** regions inside its own process, writing `k`
for `count`:

```
A = reps x round(k = 2 x count)      the measured operation, twice over
B = reps x round(k =     count)      the measured operation
C = reps x round(k = 0)              build and destroy, no measured operation
```

Both A and B run the **same code path** - same operation selector, same build,
same settle, same destruction - and differ only in the loop trip count, so
`A - B` is exactly `reps x count` executions of the measured operation.
Structure building, argument generation, process start-up, compilation and all
file IO are outside the difference.

**Why three regions, and why A is the doubled one.** The earlier two-region
form measured "the operations" against "no operations at all", so region A
ended with a structure the operations had emptied or grown while region B
ended with the one the build left behind. The two regions then did not pay the
same deallocation cost, and at large sizes that asymmetry was bigger than the
operations themselves: `A - B` came out negative and 21 rows could not be
measured at all. With `2k` against `k` both regions end in a state the
operation has been applied to, so the deallocation difference between them is
the deallocation *caused by the extra k operations* - part of what those
operations cost, on both sides, exactly as `free()` is part of what the C
reference's `remove` costs. C is the build-and-destroy control: it is what one
region costs with no measured operation at all, it is recorded for every row
(`bend_control_ns`, `reference_control_ns`), and it is what makes a difference
that is small beside its own build visible as such.

That form is still not enough for an operation that *removes* elements, and
this report says so instead of working around it quietly: what region B does
not remove inside the measured loop, the round still has to deallocate before
it ends, so part of region A's extra work is subtracted back out - and the
batch is bounded by `size` anyway, because a round can only remove what it
built. Measured on the deque, the pop difference was about 1.3 ns against a
round of ~575 ns and its sign came out at random (the previous report's FAILED
rows: `A - B` negative by hundreds of milliseconds). Removals are therefore
measured as **restoring pairs**; see the flag below.

For an operation that *adds* elements the `k` operations that `A - B` isolates
are the ones between the `k`-th and the `2k`-th of a round, so they run at
sizes `size + k .. size + 2k` rather than at `size .. size + k`, with `k`
capped at `size`. Both sides do exactly that, from the identical starting
structure and the identical argument stream, so the comparison stays
same-algorithm and same-workload; the row's `size` is the size the round was
*built* to, as before. For an operation that *removes* elements the measured
loop is a restoring pair and the structure simply stays at `size`.

**Where the two sides genuinely differ: growth.** `Base.Array` doubling on the
Bend side is `ANode{arr, empty_slots(depth)}` - one node and one fresh empty
half, the old block is *shared, not copied* - while the C references double a
contiguous buffer and `memcpy` the old half into it (the comment in
`benchmarks/native/dynamic_array.c` assumes the Bend side copies too; it does
not). The cost shows up on the other side of the ledger: an array built by
repeated doubling is a shallow tree of blocks, so Bend's indexed access grows
slightly with depth (`dynamic_array.get`: 1.9 ns at size 64, 2.2 ns at
262144) where C's is a shift and a load. Both are standard implementations of
a growable array, and each row says which of the two effects it is measuring:
rows dominated by pushes across a doubling boundary favour Bend by about one
element copy per push, rows dominated by indexing favour C by the tree walk.
No row was tuned to hide either.

**Region order is alternated.** A machine that drifts - frequency scaling,
thermal, another process - makes whatever runs last look slower, which is a
systematic bias of exactly the shape `A - B` measures. `argv[5]` selects the
order in which the three regions run (`ABC` or `CBA`); the runner alternates
it over the samples, so a monotone drift cancels between them. Every sample is
recorded with the order it ran in.

`verified` is true only when the Bend and C checksums of **all three** regions
agree, which they cannot unless both performed the same work on the same
values.

## Measurement integrity

* **No clamping, no floors.** There is no `max(delta, one_tick)` anywhere.
* Bend's runtime only exposes a millisecond clock (`IO.now`), so the batch is
  lengthened until `A - B` is at least **50 ms on the Bend side** (>= 50 clock
  ticks, i.e. at most 2% quantisation) **and** at least **100 us on the
  reference side** (thousands of `clock_gettime` ticks), with a x2 headroom so
  run-to-run variation cannot push a sample below the minimum.
* **How the batch grows matters.** For a *size-preserving* operation the batch
  grows in `count` - more operations inside one round - so the structure is
  still built exactly `reps` times and a large structure with a cheap
  operation stays measurable. A *size-changing* operation (push, insert,
  add_vertex, clear, reserve, ...) grows in whole rounds first, because a
  longer batch would no longer be that operation at that size; only when the
  round cap or the region budget is reached without a timeable difference does
  the runner also lengthen the batch inside a round, and then never past the
  row's cap: `size` for an operation that adds elements (region A at most
  trebles the structure) and `size / 2` for one that removes them (region A is
  then exactly the full sweep and never runs on an exhausted structure).
  `benchmarks/workloads.py` classifies every operation and the classification
  is recorded per row (`grow`, `method`), together with the `count` and `reps`
  that were actually used.
* A row whose difference cannot be driven above those minima - including any
  row whose difference comes out zero or negative - is a **FAILED
  MEASUREMENT**. It is reported as such, with the raw numbers and the reason,
  and never as a number.
* `operations_per_sample` (= `reps x count`) is recorded per row; every sample
  is listed individually as well as the median.
* The C references use the standard DoNotOptimize barrier
  (`benchmarks/native/common.h` `keep`) once per iteration, so a query whose result
  is loop-invariant (min, max, length, to_list, new) is actually executed
  `count` times instead of being hoisted out of the loop.

## Two caveats that are flagged per row, not hidden

**`argument-free`** - an operation that takes no varying argument (`length`,
`capacity`, `new`, `count`, `min`, `max`, `to_list`, `vertices`, `edges`,
`component_count`, `peek*`) is *loop invariant*: repeating it `count` times on
an unchanged structure is not the same as performing it `count` times. The C
side is forced to redo the work by the DoNotOptimize barrier; Bend's
interaction net could in principle share the result of the first evaluation
across the whole loop. Under the three-region form that sharing is
**self-detecting**: region A runs the loop `2k` times and region B `k` times,
so a shared result makes the two regions cost the same and the row FAILS as
unmeasurable instead of reporting a number. A row that is measured therefore
did scale with the trip count. The flag is kept because it still marks the
rows where that is the thing to check.

**`barrier-dominated`** - when the C reference costs only a couple of
nanoseconds per operation, the per-iteration DoNotOptimize barrier (which
forces the state to be spilled and reloaded) is a large fraction of what is
being timed. Rows whose reference median is at or below 3 ns/op are marked
`barrier-dominated`; a ratio below 1 in such a row is an artefact of the
barrier, not a Bend win.

**`restoring pair`** - an operation that REMOVES elements (`pop`, `pop_front`,
`pop_back`, `dequeue`, `remove`) cannot be isolated by this difference at all:
a round can only remove what it built, so the batch is bounded by `size` while
the round also pays to build those `size` elements, and `A - B` stays a small
fraction of the round. In the previous report that is exactly what the FAILED
rows were - differences at or below zero for every pop row. Such an operation
is therefore measured inside a **restoring pair**: the driver runs the removal
together with the insertion that puts the element back, on **both** sides, so
the structure keeps its size and the batch can be lengthened like any
size-preserving row. The nanoseconds reported for such a row are the *pair's*,
charged to the removal: it over-charges the Bend side by one insertion and
never flatters it, and the ratio compares identical work. Every row that was
measured this way is marked `restoring pair` in the tables below, and the
report's `method` field records it per row.

None of the three flags changes the verdict: it rests on the many rows with a
varying argument and a reference cost well above the barrier.

## A known bias in the reference, in Bend's favour

`src/balanced_search_tree.bend` and `src/prefix_trie.bend` keep their entry
count (and return the previous value) *inside the single walk* an insert or a
remove already performs. The C drivers do not: they call `rb_find` / `tn_find`
first and `rb_insert` / `rb_remove` / `tn_ins` / `tn_rem` afterwards, i.e. they
walk the tree twice where the Bend side walks it once
(`benchmarks/native/balanced_search_tree.c` lines 28, 39, 63;
`benchmarks/native/prefix_trie.c` lines 235, 257). On those rows the reference
is therefore up to about a factor of two SLOWER than it needs to be, which
makes the reported ratios for `balanced_search_tree.insert`/`remove` and
`prefix_trie.remove` *better* for Bend than a fully optimized reference would
give. It is left in this report because fixing it moves those ratios in the
direction that is bad for Bend and they are already far over the limit, so no
verdict depends on it - but it is a bias in Bend's favour and it is flagged
here rather than left for a reader to find.

## Where the red-black tree's required cases are exercised

The contract asks for empty/singleton, duplicate keys, absent removal, root
removal, ordered and reverse-ordered insertion and adversarial mixed
delete/insert histories. They are covered as follows:

| case | where |
|---|---|
| empty | benchmark rows `edge-empty` (size 0) for every tree operation, on both sides |
| singleton and small/medium/large | benchmark rows `small` (64), `medium` (4096), `large` (131072) |
| duplicate keys | inherent to the benchmark: keys are drawn from `0 .. size`, and `count` is far larger than `size` on the small/medium rows, so most measured inserts replace an existing key |
| absent removal | likewise inherent: `remove` draws from `0 .. size` against a tree of `size` keys, so a large fraction of the measured removals miss |
| root removal, ordered insertion, reverse-ordered insertion, adversarial mixed delete/insert histories | `tools/scenarios.py` `STRUCTURAL`, run by `tools/validate.py` against the real Bend binary with the red-black structural invariants re-derived after **every** operation, and included in the mutation set |

The structural histories live in the correctness harness rather than the timing
table because what they test is the shape of the tree after each operation, not
its throughput; the timing table measures each operation at three nonempty
sizes plus its empty edge case.

## Representation policy: persistent Bend vs mutating C

Seven of the structures - `dynamic_array`, `deque`, `queue`, `bitset`,
`union_find`, `fenwick_tree` and `segment_tree` - are backed by native
`Base.Array`, which is a **linear** flat array with O(1) indexed read and
write: they are threaded (every operation returns the structure) and updated
in place, exactly like their C references. The other five are **persistent**:
an update returns a new value and shares what it did not have to rebuild,
because that is what the proofs are about and what the language's runtime
provides for `Data` types. The C references implement the **same algorithm**
with the same asymptotics but mutate and reuse nodes in place, because that is
what an optimized C implementation of that algorithm does; each reference
header says so explicitly. Concretely:

| structure | Bend representation | C reference | why the comparison is still same-algorithm |
|---|---|---|---|
| `dynamic_array` | `Base.Array` of slots, capacity `2^depth`, doubling | flat buffer, doubling | identical growth policy and amortised bounds |
| `deque`, `queue` | `Base.Array` block, elements in the window `[lo, lo + len)`, block doubled at the end that runs out | the same windowed block, doubled the same way | identical index arithmetic; both O(1) amortised at both ends |
| `bitset` | `Base.Array` of packed `U32` words | flat `U32` array | identical packed-word representation |
| `union_find` | three parallel `Base.Array`s (parent, size, members) | flat arrays of the same three fields | identical union-by-size relinking |
| `fenwick_tree` | one `Base.Array` of cells, flat split-point layout | flat array, same index arithmetic | identical walks |
| `segment_tree` | two `Base.Array`s (sums, lazy tags), same layout | two flat arrays, same recursion | identical lazy propagation |
| `binary_heap` | `Base.Array` block, elements in slots `[0, size)`, children `2i+1`/`2i+2`, block doubled when full | flat array heap, same indices, same doubling | identical sift order and identical array operations per level |
| `balanced_search_tree` | red-black tree of `Node{color, l, entry, r}` | the same red-black algorithm, nodes reused in place (`benchmarks/native/redblack.h`) | identical rotations, identical fixup cases, identical order |
| `prefix_trie` | trie nodes `TNode{c, val, down, next}` (children as a sibling chain) | the same sibling chains | identical traversal |
| `doubly_linked_list` | `Base.OrdMap` node store keyed by handle, each node holding prev/next handles | arena of node records + the same ordered map | identical handle semantics (ids never reused, stale/foreign rejected) |
| `graph` | `Base.OrdMap` of vertex to `Base.OrdMap` neighbour set | the same two ordered maps | identical adjacency representation |

The first seven rows are array-backed on both sides and are the rows where
the two implementations really do the same thing to the same bytes. The last
four keep `Data` nodes on the Bend side
because their algorithm needs the links (tree and trie children, DLL
prev/next) - `docs/ARCHITECTURE.md` has the full representation table and its
self-audit - and there the Bend side pays for allocating the nodes on the path
it rebuilds where the C side overwrites them.

That is a property of the representation the proofs are about, not a handicap
added to the benchmark: the C reference is the fastest reasonable implementation of the
same algorithm, which is exactly what the contract asks for. The cost-model
table above quantifies exactly what that costs per node, and the two
array-backed structures show what the same harness measures when the
representations do match.


## Environment

* **cpu**: Apple M4 (10 logical cores; benchmarks pinned to one Bend worker thread)
* **os**: Darwin 24.6.0 arm64
* **bend_compiler**: bend 2.0.16 (/Users/monkeair/.bend/bin/bend, sha256 da9bc51449f04a65bf633351fb754cd6f883f5f5d9ab0c4e947f5c6f19eb7386)
* **reference_compiler**: Apple clang version 17.0.0 (clang-1700.6.3.2)
* **bend_flags**: -o <bin> (native C backend); run with --threads 1
* **reference_flags**: -O3 -march=native -std=c11 -fno-strict-aliasing
* **reference_revision**: benchmarks/native/ in this workspace, sha256 of every
file recorded in source_sha256

> The machine was **not idle** during this run: unrelated processes were
> using whole cores throughout. The runner rejects unusable measurements
> rather than reporting them, but the surviving numbers still carry that
> noise. Re-run on an idle machine for publication-quality figures.

## Verdict

| | rows |
|---|---|
| measured, within 2.5x | 199 |
| measured, **over 2.5x** | 200 |
| of those, unflagged (varying argument, reference > 3 ns/op) | 102 |
| FAILED measurement (not resolvable above the clock minima) | 9 |
| total rows in `benchmarks/workloads.py` | 408 |

**The 2.5x contract is NOT met.** 200 measured workloads exceed it
(worst unflagged row: `prefix_trie.longest_prefix` / edge-empty at **53.68x**;
worst row of any kind: `prefix_trie.contains` / edge-empty at **120.57x**)
and 9 workloads could not be measured at all. The nine `lru.*`
operations the contract requires have **no rows**: the retained LRU
cannot be compiled to a native binary with this toolchain (see
`docs/VALIDATION.md`, "arity over 255"), and substituting a
non-native backend would not be a native-C measurement.

## All rows

`bend` and `ref` are nanoseconds per operation (median of the samples).

### `balanced_search_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 300000 | 421.67 | 30.16 | 13.98x **over** | yes | - |
| `insert` | medium | 4096 | 250000 | 1158.00 | 79.14 | 14.63x **over** | yes | - |
| `insert` | large | 131072 | 100000 | 1795.00 | 189.95 | 9.45x **over** | yes | - |
| `remove` | small | 64 | 200000 | 895.00 | 71.92 | 12.44x **over** | yes | restoring pair |
| `remove` | medium | 4096 | 100000 | 1950.00 | 154.75 | 12.60x **over** | yes | restoring pair |
| `remove` | large | 131072 | 80000 | 2568.75 | 279.52 | 9.19x **over** | yes | restoring pair |
| `lookup` | small | 64 | 1400000 | 136.07 | 19.78 | 6.88x **over** | yes | - |
| `lookup` | medium | 4096 | 400000 | 292.50 | 46.06 | 6.35x **over** | yes | - |
| `lookup` | large | 131072 | 200000 | 527.50 | 105.21 | 5.01x **over** | yes | - |
| `contains` | small | 64 | 1400000 | 141.79 | 21.04 | 6.74x **over** | yes | - |
| `contains` | medium | 4096 | 400000 | 302.50 | 47.58 | 6.36x **over** | yes | - |
| `contains` | large | 131072 | 420000 | 547.62 | 110.81 | 4.94x **over** | yes | - |
| `min` | small | 64 | 3000000 | 42.67 | 1.29 | 32.97x **over** | yes | argument-free, barrier-dominated |
| `min` | medium | 4096 | 800000 | 139.38 | 5.20 | 26.79x **over** | yes | argument-free |
| `min` | large | 131072 | 1500000 | 156.00 | 6.01 | 25.94x **over** | yes | argument-free |
| `max` | small | 64 | 4000000 | 49.75 | 1.23 | 40.37x **over** | yes | argument-free, barrier-dominated |
| `max` | medium | 4096 | 900000 | 133.33 | 4.46 | 29.89x **over** | yes | argument-free |
| `max` | large | 131072 | 3200000 | 179.38 | 5.59 | 32.08x **over** | yes | argument-free |
| `lower_bound` | small | 64 | 800000 | 137.50 | 20.25 | 6.79x **over** | yes | - |
| `lower_bound` | medium | 4096 | 600000 | 309.17 | 46.41 | 6.66x **over** | yes | - |
| `lower_bound` | large | 131072 | 680000 | 485.29 | 100.72 | 4.82x **over** | yes | - |
| `range` | small | 64 | 512000 | 250.00 | 38.94 | 6.42x **over** | yes | - |
| `range` | medium | 4096 | 12600 | 11865.08 | 1009.80 | 11.75x **over** | yes | - |
| `range` | large | 131072 | 1280 | 155859.38 | 9117.97 | 17.09x **over** | yes | - |
| `to_list` | small | 64 | 256000 | 802.73 | 61.70 | 13.01x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 1500 | 77666.67 | 4830.00 | 16.08x **over** | yes | argument-free |
| `to_list` | large | 131072 | 300 | 2576666.67 | 243896.67 | 10.56x **over** | yes | argument-free |
| `length` | small | 64 | 179200000 | 1.09 | 3.16 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.11 | 3.16 | 0.35x | yes | argument-free |
| `length` | large | 131072 | 169000000 | 1.07 | 3.25 | 0.33x | yes | argument-free |
| `new` | small | 64 | 89600000 | 1.10 | 2.77 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 102400000 | 1.09 | 2.77 | 0.39x | yes | argument-free, barrier-dominated |
| `new` | large | 131072 | 204800000 | 1.32 | 3.10 | 0.43x | yes | argument-free |
| `new` | edge-empty | 0 | 83200000 | 1.24 | 3.14 | 0.39x | yes | argument-free |
| `length` | edge-empty | 0 | 96000000 | 1.19 | 3.44 | 0.35x | yes | argument-free |
| `insert` | edge-empty | 0 | 3400000 | 42.65 | 3.38 | 12.60x **over** | yes | - |
| `remove` | edge-empty | 0 | 19200000 | 7.14 | 3.06 | 2.33x | yes | - |
| `lookup` | edge-empty | 0 | 25600000 | 4.69 | 1.46 | 3.20x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 25600000 | 4.49 | 1.34 | 3.36x **over** | yes | barrier-dominated |
| `min` | edge-empty | 0 | 32000000 | 4.11 | 1.32 | 3.11x **over** | yes | argument-free, barrier-dominated |
| `max` | edge-empty | 0 | 51200000 | 4.28 | 1.27 | 3.37x **over** | yes | argument-free, barrier-dominated |
| `lower_bound` | edge-empty | 0 | 19200000 | 6.25 | 1.30 | 4.81x **over** | yes | barrier-dominated |
| `range` | edge-empty | 0 | 20400000 | 5.25 | 5.22 | 1.01x | yes | - |
| `to_list` | edge-empty | 0 | 25600000 | 5.21 | 4.02 | 1.30x | yes | argument-free |

### `binary_heap`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 10200000 | 20.83 | 13.26 | 1.57x | yes | - |
| `push` | medium | 4096 | 5100000 | 20.10 | 11.82 | 1.70x | yes | - |
| `push` | large | 131072 | 6684672 | 20.35 | 10.79 | 1.89x | yes | - |
| `peek` | small | 64 | 89600000 | 1.16 | 1.18 | 0.98x | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 96000000 | 1.16 | 1.22 | 0.95x | yes | argument-free, barrier-dominated |
| `peek` | large | 131072 | 108800000 | 1.13 | 1.13 | 1.00x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 89600000 | 1.24 | 3.62 | 0.34x | yes | argument-free |
| `length` | medium | 4096 | 115200000 | 1.09 | 3.04 | 0.36x | yes | argument-free |
| `length` | large | 131072 | 108800000 | 1.08 | 3.12 | 0.35x | yes | argument-free |
| `from_list` | small | 64 | 1050000 | 134.76 | 62.94 | 2.14x | yes | - |
| `from_list` | medium | 4096 | 850000 | 137.06 | 67.89 | 2.02x | yes | - |
| `from_list` | large | 131072 | 1040000 | 134.62 | 68.89 | 1.95x | yes | - |
| `to_sorted_list` | small | 64 | 102000 | 1387.25 | 607.00 | 2.29x | yes | argument-free |
| `to_sorted_list` | medium | 4096 | 700 | 168571.43 | 78172.86 | 2.16x | yes | argument-free |
| `to_sorted_list` | large | 131072 | 15 | 10266666.67 | 4324466.67 | 2.37x | yes | argument-free |
| `pop` | small | 64 | 3400000 | 40.74 | 17.35 | 2.35x | yes | restoring pair |
| `pop` | medium | 4096 | 2100000 | 83.10 | 36.80 | 2.26x | yes | restoring pair |
| `pop` | large | 131072 | 1020000 | 137.75 | 52.82 | 2.61x **over** | yes | restoring pair |
| `new` | small | 64 | 40800000 | 3.27 | 2.95 | 1.11x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 38400000 | 3.29 | 2.93 | 1.13x | yes | argument-free, barrier-dominated |
| `new` | large | 131072 | 64000000 | 3.34 | 2.97 | 1.12x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 32000000 | 3.20 | 3.16 | 1.01x | yes | argument-free |
| `length` | edge-empty | 0 | 96000000 | 1.10 | 3.18 | 0.35x | yes | argument-free |
| `push` | edge-empty | 0 | 6800000 | 18.38 | 12.24 | 1.50x | yes | - |
| `peek` | edge-empty | 0 | 83200000 | 1.12 | 1.13 | 0.99x | yes | argument-free, barrier-dominated |
| `pop` | edge-empty | 0 | 166400000 | 1.15 | 1.18 | 0.98x | yes | barrier-dominated |
| `from_list` | edge-empty | 0 | 900000 | 125.56 | 62.17 | 2.02x | yes | - |
| `to_sorted_list` | edge-empty | 0 | 12800000 | 10.94 | 5.13 | 2.13x | yes | argument-free |

### `bitset`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `set` | small | 64 | 76800000 | 1.77 | 1.64 | 1.08x | yes | barrier-dominated |
| `set` | medium | 4096 | 70400000 | 1.53 | 1.40 | 1.09x | yes | barrier-dominated |
| `set` | large | 262144 | 67200000 | 1.52 | 1.38 | 1.10x | yes | barrier-dominated |
| `clear` | small | 64 | 64000000 | 1.63 | 1.56 | 1.05x | yes | barrier-dominated |
| `clear` | medium | 4096 | 70400000 | 1.51 | 1.37 | 1.10x | yes | barrier-dominated |
| `clear` | large | 262144 | 67200000 | 1.61 | 1.49 | 1.08x | yes | barrier-dominated |
| `get` | small | 64 | 64000000 | 1.96 | 1.67 | 1.17x | yes | barrier-dominated |
| `get` | medium | 4096 | 64000000 | 1.73 | 1.38 | 1.25x | yes | barrier-dominated |
| `get` | large | 262144 | 96000000 | 1.71 | 1.35 | 1.27x | yes | barrier-dominated |
| `count` | small | 64 | 1700000 | 60.00 | 4.75 | 12.63x **over** | yes | argument-free |
| `count` | medium | 4096 | 40000 | 3625.00 | 229.53 | 15.79x **over** | yes | argument-free |
| `count` | large | 262144 | 500 | 226000.00 | 14450.00 | 15.64x **over** | yes | argument-free |
| `length` | small | 64 | 89600000 | 1.05 | 3.02 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 166400000 | 1.12 | 3.11 | 0.36x | yes | argument-free |
| `length` | large | 262144 | 166400000 | 1.09 | 3.15 | 0.35x | yes | argument-free |
| `to_list` | small | 64 | 300000 | 368.33 | 78.96 | 4.66x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 6000 | 21083.33 | 4967.50 | 4.24x **over** | yes | argument-free |
| `to_list` | large | 262144 | 100 | 2100000.00 | 341740.00 | 6.15x **over** | yes | argument-free |
| `union` | small | 64 | 16000000 | 6.94 | 1.47 | 4.73x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 2040000 | 75.98 | 66.02 | 1.15x | yes | - |
| `union` | large | 262144 | 34000 | 3514.71 | 4374.71 | 0.80x | yes | - |
| `intersection` | small | 64 | 16000000 | 6.97 | 1.65 | 4.24x **over** | yes | barrier-dominated |
| `intersection` | medium | 4096 | 2040000 | 77.45 | 70.73 | 1.09x | yes | - |
| `intersection` | large | 262144 | 51000 | 3627.45 | 4167.61 | 0.87x | yes | - |
| `difference` | small | 64 | - | FAILED | FAILED | - | - | sample 0: A-B = 110000000ns (bend) / -16284000ns (reference), below the 50000000ns / 100000ns minima |
| `difference` | medium | 4096 | 2040000 | 68.14 | 60.25 | 1.13x | yes | - |
| `difference` | large | 262144 | 32000 | 3625.00 | 3947.33 | 0.92x | yes | - |
| `xor` | small | 64 | 16000000 | 6.78 | 1.47 | 4.62x **over** | yes | barrier-dominated |
| `xor` | medium | 4096 | - | FAILED | FAILED | - | - | sample 1: A-B = 49000000ns (bend) / 89528000ns (reference), below the 50000000ns / 100000ns minima |
| `xor` | large | 262144 | 51000 | 3862.75 | 3524.97 | 1.10x | yes | - |
| `new` | small | 64 | 38400000 | 3.42 | 12.14 | 0.28x | yes | argument-free |
| `new` | medium | 4096 | 38400000 | 3.35 | 11.97 | 0.28x | yes | argument-free |
| `new` | large | 262144 | 28800000 | 3.49 | 11.45 | 0.30x | yes | argument-free |
| `new` | edge-empty | 0 | 40800000 | 3.22 | 12.22 | 0.26x | yes | argument-free |
| `length` | edge-empty | 0 | 89600000 | 1.25 | 3.39 | 0.37x | yes | argument-free |
| `get` | edge-empty | 0 | 89600000 | 1.32 | 1.31 | 1.00x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 89600000 | 1.43 | 1.20 | 1.19x | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 76800000 | 1.52 | 1.28 | 1.18x | yes | barrier-dominated |
| `count` | edge-empty | 0 | 5200000 | 38.94 | 4.63 | 8.41x **over** | yes | argument-free |
| `union` | edge-empty | 0 | 25600000 | 5.98 | 1.46 | 4.10x **over** | yes | barrier-dominated |
| `intersection` | edge-empty | 0 | 30600000 | 5.56 | 1.28 | 4.32x **over** | yes | barrier-dominated |
| `difference` | edge-empty | 0 | 20400000 | 5.66 | 1.42 | 4.00x **over** | yes | barrier-dominated |
| `xor` | edge-empty | 0 | 25600000 | 7.48 | 1.61 | 4.64x **over** | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 4000000 | 39.38 | 4.49 | 8.78x **over** | yes | argument-free |

### `deque`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 13600000 | 6.73 | 1.39 | 4.84x **over** | yes | barrier-dominated |
| `push_front` | medium | 4096 | 19200000 | 6.22 | 1.40 | 4.44x **over** | yes | barrier-dominated |
| `push_front` | large | 262144 | 26738688 | 6.90 | 1.44 | 4.80x **over** | yes | barrier-dominated |
| `push_back` | small | 64 | 20400000 | 6.42 | 1.46 | 4.39x **over** | yes | barrier-dominated |
| `push_back` | medium | 4096 | 19200000 | 6.74 | 1.36 | 4.98x **over** | yes | barrier-dominated |
| `push_back` | large | 262144 | 13369344 | 6.81 | 1.44 | 4.72x **over** | yes | barrier-dominated |
| `peek_front` | small | 64 | 89600000 | 1.11 | 1.13 | 0.98x | yes | argument-free, barrier-dominated |
| `peek_front` | medium | 4096 | 96000000 | 1.21 | 1.22 | 0.99x | yes | argument-free, barrier-dominated |
| `peek_front` | large | 262144 | 130050000 | 1.15 | 1.19 | 0.96x | yes | argument-free, barrier-dominated |
| `peek_back` | small | 64 | 89600000 | 1.11 | 1.16 | 0.96x | yes | argument-free, barrier-dominated |
| `peek_back` | medium | 4096 | 166400000 | 1.13 | 1.22 | 0.93x | yes | argument-free, barrier-dominated |
| `peek_back` | large | 262144 | 108800000 | 1.14 | 1.17 | 0.97x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 179200000 | 1.09 | 3.06 | 0.36x | yes | argument-free |
| `length` | medium | 4096 | 134400000 | 1.09 | 3.17 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 108800000 | 1.07 | 3.14 | 0.34x | yes | argument-free |
| `to_list` | small | 64 | 200000 | 650.00 | 89.81 | 7.24x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 4000 | 30750.00 | 6415.38 | 4.79x **over** | yes | argument-free |
| `to_list` | large | 262144 | 100 | 2025000.00 | 400165.00 | 5.06x **over** | yes | argument-free |
| `pop_front` | small | 64 | 20400000 | 4.71 | 7.53 | 0.62x | yes | restoring pair |
| `pop_front` | medium | 4096 | 25600000 | 4.84 | 7.34 | 0.66x | yes | restoring pair |
| `pop_front` | large | 262144 | 25500000 | 4.61 | 7.37 | 0.63x | yes | restoring pair |
| `pop_back` | small | 64 | 25600000 | 4.73 | 7.26 | 0.65x | yes | restoring pair |
| `pop_back` | medium | 4096 | 25600000 | 4.69 | 7.25 | 0.65x | yes | restoring pair |
| `pop_back` | large | 262144 | 45900000 | 4.62 | 6.91 | 0.67x | yes | restoring pair |
| `new` | small | 64 | 38400000 | 3.53 | 1.36 | 2.60x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 30600000 | 3.32 | 1.34 | 2.48x | yes | argument-free, barrier-dominated |
| `new` | large | 262144 | 35200000 | 3.35 | 1.32 | 2.53x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 38400000 | 3.41 | 1.31 | 2.60x **over** | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 89600000 | 1.10 | 3.21 | 0.34x | yes | argument-free |
| `push_front` | edge-empty | 0 | 20400000 | 7.13 | 1.40 | 5.10x **over** | yes | barrier-dominated |
| `push_back` | edge-empty | 0 | 25600000 | 6.58 | 1.43 | 4.60x **over** | yes | barrier-dominated |
| `pop_front` | edge-empty | 0 | 89600000 | 1.11 | 1.11 | 1.00x | yes | barrier-dominated |
| `pop_back` | edge-empty | 0 | 89600000 | 1.17 | 1.17 | 1.00x | yes | barrier-dominated |
| `peek_front` | edge-empty | 0 | 89600000 | 1.17 | 1.16 | 1.01x | yes | argument-free, barrier-dominated |
| `peek_back` | edge-empty | 0 | 179200000 | 1.13 | 1.14 | 0.99x | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 20400000 | 6.35 | 1.30 | 4.90x **over** | yes | argument-free, barrier-dominated |

### `doubly_linked_list`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 100000 | 5615.00 | 330.35 | 17.00x **over** | yes | - |
| `push_front` | medium | 2048 | 50000 | 5320.00 | 279.41 | 19.04x **over** | yes | - |
| `push_front` | large | 32768 | 32768 | 5340.58 | 272.81 | 19.58x **over** | yes | - |
| `push_back` | small | 64 | 100000 | 5290.00 | 314.98 | 16.79x **over** | yes | - |
| `push_back` | medium | 2048 | 50000 | 5800.00 | 280.10 | 20.71x **over** | yes | - |
| `push_back` | large | 32768 | - | FAILED | FAILED | - | - | sample 4: A-B = 45000000ns (bend) / 3350000ns (reference), below the 50000000ns / 100000ns minima |
| `insert_before` | small | 64 | 100000 | 8715.00 | 505.67 | 17.23x **over** | yes | - |
| `insert_before` | medium | 2048 | 50000 | 7020.00 | 445.28 | 15.77x **over** | yes | - |
| `insert_before` | large | 32768 | 20000 | 7650.00 | 638.10 | 11.99x **over** | yes | - |
| `insert_after` | small | 64 | 100000 | 7500.00 | 533.46 | 14.06x **over** | yes | - |
| `insert_after` | medium | 2048 | 50000 | 7750.00 | 512.10 | 15.13x **over** | yes | - |
| `insert_after` | large | 32768 | 20000 | 8025.00 | 677.80 | 11.84x **over** | yes | - |
| `get` | small | 64 | 600000 | 209.17 | 28.32 | 7.39x **over** | yes | - |
| `get` | medium | 2048 | 300000 | 460.00 | 60.36 | 7.62x **over** | yes | - |
| `get` | large | 32768 | 280000 | 628.57 | 142.46 | 4.41x **over** | yes | - |
| `set` | small | 64 | 200000 | 707.50 | 26.55 | 26.64x **over** | yes | - |
| `set` | medium | 2048 | 100000 | 1425.00 | 54.33 | 26.23x **over** | yes | - |
| `set` | large | 32768 | 1280000 | 2229.69 | 146.42 | 15.23x **over** | yes | - |
| `next` | small | 64 | 1000000 | 185.00 | 24.54 | 7.54x **over** | yes | - |
| `next` | medium | 2048 | 3200000 | 381.56 | 49.09 | 7.77x **over** | yes | - |
| `next` | large | 32768 | 300000 | 518.33 | 146.06 | 3.55x **over** | yes | - |
| `prev` | small | 64 | 600000 | 173.33 | 24.37 | 7.11x **over** | yes | - |
| `prev` | medium | 2048 | 300000 | 330.00 | 47.66 | 6.92x **over** | yes | - |
| `prev` | large | 32768 | 360000 | 526.39 | 147.39 | 3.57x **over** | yes | - |
| `length` | small | 64 | 25600000 | 5.08 | 3.28 | 1.55x | yes | argument-free |
| `length` | medium | 2048 | 25600000 | 4.51 | 3.15 | 1.43x | yes | argument-free |
| `length` | large | 32768 | 33280000 | 4.78 | 3.17 | 1.51x | yes | argument-free |
| `to_list` | small | 64 | 10000 | 13900.00 | 263.15 | 52.82x **over** | yes | argument-free |
| `to_list` | medium | 2048 | 300 | 868333.33 | 22073.33 | 39.34x **over** | yes | argument-free |
| `to_list` | large | 32768 | 20 | 18275000.00 | 1170750.00 | 15.61x **over** | yes | argument-free |
| `remove` | small | 64 | - | FAILED | FAILED | - | - | sample 0: A-B = 15000000ns (bend) / 5536000ns (reference), below the 50000000ns / 100000ns minima |
| `remove` | medium | 2048 | 69632 | 1809.51 | 109.86 | 16.47x **over** | yes | - |
| `remove` | large | 32768 | 49152 | 2543.13 | 224.89 | 11.31x **over** | yes | - |
| `new` | small | 64 | 83200000 | 1.21 | 3.09 | 0.39x | yes | argument-free |
| `new` | medium | 2048 | 153600000 | 1.16 | 2.97 | 0.39x | yes | argument-free, barrier-dominated |
| `new` | large | 32768 | 83200000 | 1.24 | 2.90 | 0.43x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 83200000 | 1.08 | 2.69 | 0.40x | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 96000000 | 1.11 | 2.79 | 0.40x | yes | argument-free, barrier-dominated |
| `push_front` | edge-empty | 0 | 100000 | 5510.00 | 316.48 | 17.41x **over** | yes | - |
| `push_back` | edge-empty | 0 | 100000 | 4715.00 | 273.90 | 17.21x **over** | yes | - |
| `insert_before` | edge-empty | 0 | 12800000 | 11.29 | 1.30 | 8.71x **over** | yes | barrier-dominated |
| `insert_after` | edge-empty | 0 | 12800000 | 11.09 | 1.26 | 8.82x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 12800000 | 9.57 | 1.22 | 7.86x **over** | yes | barrier-dominated |
| `get` | edge-empty | 0 | 15300000 | 10.39 | 1.28 | 8.14x **over** | yes | barrier-dominated |
| `set` | edge-empty | 0 | 12800000 | 9.92 | 1.22 | 8.14x **over** | yes | barrier-dominated |
| `next` | edge-empty | 0 | 25600000 | 4.55 | 1.22 | 3.74x **over** | yes | barrier-dominated |
| `prev` | edge-empty | 0 | 25600000 | 4.67 | 1.26 | 3.71x **over** | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 19200000 | 8.15 | 4.43 | 1.84x | yes | argument-free |

### `dynamic_array`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 20400000 | 6.99 | 3.88 | 1.80x | yes | - |
| `push` | medium | 4096 | 20400000 | 6.81 | 3.81 | 1.79x | yes | - |
| `push` | large | 262144 | 16777216 | 7.36 | 4.66 | 1.58x | yes | - |
| `get` | small | 64 | 64000000 | 1.95 | 1.66 | 1.17x | yes | barrier-dominated |
| `get` | medium | 4096 | 64000000 | 1.84 | 1.47 | 1.25x | yes | barrier-dominated |
| `get` | large | 262144 | 53550000 | 2.11 | 1.46 | 1.44x | yes | barrier-dominated |
| `set` | small | 64 | 64000000 | 1.67 | 1.53 | 1.09x | yes | barrier-dominated |
| `set` | medium | 4096 | 70400000 | 1.48 | 1.38 | 1.07x | yes | barrier-dominated |
| `set` | large | 262144 | 83200000 | 1.74 | 1.74 | 1.00x | yes | barrier-dominated |
| `length` | small | 64 | 128000000 | 1.09 | 3.15 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.09 | 3.21 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 83200000 | 1.20 | 3.37 | 0.36x | yes | argument-free |
| `capacity` | small | 64 | 179200000 | 1.07 | 2.73 | 0.39x | yes | argument-free, barrier-dominated |
| `capacity` | medium | 4096 | 166400000 | 1.08 | 2.67 | 0.41x | yes | argument-free, barrier-dominated |
| `capacity` | large | 262144 | 163200000 | 1.17 | 2.93 | 0.40x | yes | argument-free, barrier-dominated |
| `reserve` | small | 64 | 38400000 | 4.36 | 1.38 | 3.16x **over** | yes | barrier-dominated |
| `reserve` | medium | 4096 | 25600000 | 4.18 | 1.33 | 3.15x **over** | yes | barrier-dominated |
| `reserve` | large | 262144 | 25600000 | 4.20 | 1.34 | 3.13x **over** | yes | barrier-dominated |
| `to_list` | small | 64 | 200000 | 590.00 | 92.48 | 6.38x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 4000 | 31625.00 | 4971.75 | 6.36x **over** | yes | argument-free |
| `to_list` | large | 262144 | 100 | 1925000.00 | 377920.00 | 5.09x **over** | yes | argument-free |
| `clear` | small | 64 | 2600000 | 55.77 | 6.93 | 8.05x **over** | yes | - |
| `clear` | medium | 4096 | 40000 | 3050.00 | 638.61 | 4.78x **over** | yes | - |
| `clear` | large | 262144 | 1000 | 204000.00 | 15053.00 | 13.55x **over** | yes | - |
| `pop` | small | 64 | 25600000 | 5.31 | 4.09 | 1.30x | yes | restoring pair |
| `pop` | medium | 4096 | 38400000 | 5.14 | 3.79 | 1.36x | yes | restoring pair |
| `pop` | large | 262144 | 22950000 | 5.25 | 3.33 | 1.57x | yes | restoring pair |
| `new` | small | 64 | 25600000 | 4.22 | 2.89 | 1.46x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 30600000 | 4.28 | 2.97 | 1.44x | yes | argument-free, barrier-dominated |
| `new` | large | 262144 | 28050000 | 4.35 | 2.96 | 1.47x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 25600000 | 4.18 | 2.93 | 1.43x | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 102400000 | 1.07 | 2.98 | 0.36x | yes | argument-free, barrier-dominated |
| `capacity` | edge-empty | 0 | 179200000 | 1.13 | 2.74 | 0.41x | yes | argument-free, barrier-dominated |
| `get` | edge-empty | 0 | 76800000 | 1.35 | 1.18 | 1.14x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 89600000 | 1.22 | 1.17 | 1.05x | yes | barrier-dominated |
| `push` | edge-empty | 0 | 20400000 | 6.42 | 3.88 | 1.65x | yes | - |
| `pop` | edge-empty | 0 | 89600000 | 1.11 | 1.11 | 1.00x | yes | barrier-dominated |
| `reserve` | edge-empty | 0 | 38400000 | 4.21 | 1.25 | 3.36x **over** | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 61200000 | 4.05 | 2.22 | 1.82x | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 25600000 | 5.02 | 2.19 | 2.30x | yes | argument-free, barrier-dominated |

### `fenwick_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add` | small | 64 | 6400000 | 22.03 | 19.58 | 1.13x | yes | - |
| `add` | medium | 4096 | 2550000 | 40.78 | 36.87 | 1.11x | yes | - |
| `add` | large | 262144 | 2040000 | 57.35 | 51.39 | 1.12x | yes | - |
| `prefix_sum` | small | 64 | 6800000 | 22.35 | 19.17 | 1.17x | yes | - |
| `prefix_sum` | medium | 4096 | 3200000 | 41.56 | 37.30 | 1.11x | yes | - |
| `prefix_sum` | large | 262144 | 2040000 | 58.09 | 52.57 | 1.10x | yes | - |
| `range_sum` | small | 64 | 6800000 | 23.38 | 19.92 | 1.17x | yes | - |
| `range_sum` | medium | 4096 | 3200000 | 42.03 | 37.80 | 1.11x | yes | - |
| `range_sum` | large | 262144 | 12800000 | 16.33 | 14.28 | 1.14x | yes | - |
| `length` | small | 64 | 102400000 | 1.06 | 3.07 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 108800000 | 1.09 | 3.11 | 0.35x | yes | argument-free |
| `length` | large | 262144 | 108800000 | 1.10 | 3.13 | 0.35x | yes | argument-free |
| `from_list` | small | 64 | 750000 | 147.33 | 30.42 | 4.84x **over** | yes | - |
| `from_list` | medium | 4096 | 750000 | 150.00 | 27.47 | 5.46x **over** | yes | - |
| `from_list` | large | 262144 | 1360000 | 147.06 | 26.84 | 5.48x **over** | yes | - |
| `new` | small | 64 | 12800000 | 8.91 | 12.47 | 0.71x | yes | argument-free |
| `new` | medium | 4096 | 12800000 | 7.81 | 13.64 | 0.57x | yes | argument-free |
| `new` | large | 262144 | 16000000 | 8.34 | 12.62 | 0.66x | yes | argument-free |
| `new` | edge-empty | 0 | 19200000 | 8.20 | 13.46 | 0.61x | yes | argument-free |
| `from_list` | edge-empty | 0 | 700000 | 172.86 | 33.16 | 5.21x **over** | yes | - |
| `length` | edge-empty | 0 | 76800000 | 1.22 | 3.55 | 0.34x | yes | argument-free |
| `add` | edge-empty | 0 | 38400000 | 2.46 | 1.48 | 1.66x | yes | barrier-dominated |
| `prefix_sum` | edge-empty | 0 | 44800000 | 3.16 | 1.74 | 1.81x | yes | barrier-dominated |
| `range_sum` | edge-empty | 0 | 25600000 | 4.30 | 1.95 | 2.20x | yes | barrier-dominated |

### `graph`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add_vertex` | small | 32 | 750000 | 170.00 | 22.77 | 7.47x **over** | yes | - |
| `add_vertex` | medium | 512 | 600000 | 285.00 | 38.54 | 7.39x **over** | yes | - |
| `add_vertex` | large | 4096 | - | FAILED | FAILED | - | - | sample 3: A-B = -108000000ns (bend) / 14621000ns (reference), below the 50000000ns / 100000ns minima |
| `remove_vertex` | small | 32 | - | FAILED | FAILED | - | - | sample 4: A-B = -44000000ns (bend) / 21446000ns (reference), below the 50000000ns / 100000ns minima |
| `remove_vertex` | medium | 512 | 969000 | 1974.72 | 204.64 | 9.65x **over** | yes | - |
| `remove_vertex` | large | 4096 | 400 | 280000.00 | 30672.50 | 9.13x **over** | yes | - |
| `add_edge` | small | 32 | 50000 | 1950.00 | 84.83 | 22.99x **over** | yes | - |
| `add_edge` | medium | 512 | 40000 | 4625.00 | 427.85 | 10.81x **over** | yes | - |
| `add_edge` | large | 4096 | 30000 | 3766.67 | 419.68 | 8.98x **over** | yes | - |
| `remove_edge` | small | 32 | 350000 | 270.00 | 35.76 | 7.55x **over** | yes | - |
| `remove_edge` | medium | 512 | 200000 | 580.00 | 82.94 | 6.99x **over** | yes | - |
| `remove_edge` | large | 4096 | 120000 | 845.83 | 124.45 | 6.80x **over** | yes | - |
| `has_vertex` | small | 32 | 1500000 | 140.00 | 19.96 | 7.01x **over** | yes | - |
| `has_vertex` | medium | 512 | 520000 | 241.35 | 37.32 | 6.47x **over** | yes | - |
| `has_vertex` | large | 4096 | 510000 | 399.02 | 51.29 | 7.78x **over** | yes | - |
| `has_edge` | small | 32 | 600000 | 325.00 | 42.17 | 7.71x **over** | yes | - |
| `has_edge` | medium | 512 | 320000 | 557.81 | 76.13 | 7.33x **over** | yes | - |
| `has_edge` | large | 4096 | 150000 | 833.33 | 123.83 | 6.73x **over** | yes | - |
| `neighbors` | small | 32 | 1100000 | 185.00 | 23.15 | 7.99x **over** | yes | - |
| `neighbors` | medium | 512 | 520000 | 309.62 | 39.74 | 7.79x **over** | yes | - |
| `neighbors` | large | 4096 | 510000 | 477.45 | 66.02 | 7.23x **over** | yes | - |
| `vertices` | small | 32 | 130000 | 957.69 | 38.60 | 24.81x **over** | yes | argument-free |
| `vertices` | medium | 512 | 7500 | 15866.67 | 674.93 | 23.51x **over** | yes | argument-free |
| `vertices` | large | 4096 | 850 | 150000.00 | 5307.65 | 28.26x **over** | yes | argument-free |
| `edges` | small | 32 | 40000 | 2937.50 | 160.24 | 18.33x **over** | yes | argument-free |
| `edges` | medium | 512 | 2000 | 57500.00 | 2835.00 | 20.28x **over** | yes | argument-free |
| `edges` | large | 4096 | 300 | 605000.00 | 24953.33 | 24.25x **over** | yes | argument-free |
| `new` | small | 32 | 20400000 | 5.07 | 2.13 | 2.39x | yes | argument-free, barrier-dominated |
| `new` | medium | 512 | 25600000 | 4.94 | 2.18 | 2.27x | yes | argument-free, barrier-dominated |
| `new` | large | 4096 | 38400000 | 5.57 | 2.20 | 2.54x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 25600000 | 5.25 | 2.13 | 2.46x | yes | argument-free, barrier-dominated |
| `add_vertex` | edge-empty | 0 | 6800000 | 30.22 | 1.44 | 21.00x **over** | yes | barrier-dominated |
| `remove_vertex` | edge-empty | 0 | 12800000 | 8.91 | 1.36 | 6.54x **over** | yes | barrier-dominated |
| `add_edge` | edge-empty | 0 | 10200000 | 15.98 | 1.41 | 11.31x **over** | yes | barrier-dominated |
| `remove_edge` | edge-empty | 0 | - | FAILED | FAILED | - | - | sample 4: A-B = 255000000ns (bend) / -9964000ns (reference), below the 50000000ns / 100000ns minima |
| `has_vertex` | edge-empty | 0 | 19200000 | 7.01 | 1.33 | 5.25x **over** | yes | barrier-dominated |
| `has_edge` | edge-empty | 0 | 10200000 | 19.41 | 1.75 | 11.08x **over** | yes | barrier-dominated |
| `neighbors` | edge-empty | 0 | 12800000 | 8.63 | 1.30 | 6.66x **over** | yes | barrier-dominated |
| `vertices` | edge-empty | 0 | 19200000 | 5.16 | 3.96 | 1.30x | yes | argument-free |
| `edges` | edge-empty | 0 | 25600000 | 5.80 | 4.71 | 1.23x | yes | argument-free |

### `prefix_trie`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 150000 | 1073.33 | 202.05 | 5.31x **over** | yes | - |
| `insert` | medium | 2048 | 120000 | 920.83 | 145.83 | 6.31x **over** | yes | - |
| `insert` | large | 32768 | 196608 | 930.79 | 215.67 | 4.32x **over** | yes | - |
| `lookup` | small | 64 | 500000 | 308.00 | 31.87 | 9.67x **over** | yes | - |
| `lookup` | medium | 2048 | 400000 | 430.00 | 68.93 | 6.24x **over** | yes | - |
| `lookup` | large | 32768 | 640000 | 843.75 | 118.41 | 7.13x **over** | yes | - |
| `remove` | small | 64 | 200000 | 720.00 | 96.15 | 7.49x **over** | yes | restoring pair |
| `remove` | medium | 2048 | 100000 | 995.00 | 136.47 | 7.29x **over** | yes | restoring pair |
| `remove` | large | 32768 | 640000 | 1450.78 | 223.44 | 6.49x **over** | yes | restoring pair |
| `contains` | small | 64 | 600000 | 337.50 | 35.30 | 9.56x **over** | yes | - |
| `contains` | medium | 2048 | 260000 | 482.69 | 67.55 | 7.15x **over** | yes | - |
| `contains` | large | 32768 | 510000 | 779.41 | 125.97 | 6.19x **over** | yes | - |
| `prefix_entries` | small | 64 | 85000 | 1688.24 | 111.63 | 15.12x **over** | yes | - |
| `prefix_entries` | medium | 2048 | 2000 | 55250.00 | 3007.50 | 18.37x **over** | yes | - |
| `prefix_entries` | large | 32768 | 120 | 1712500.00 | 47616.67 | 35.96x **over** | yes | - |
| `longest_prefix` | small | 64 | 400000 | 293.75 | 37.33 | 7.87x **over** | yes | - |
| `longest_prefix` | medium | 2048 | 480000 | 379.17 | 73.48 | 5.16x **over** | yes | - |
| `longest_prefix` | large | 32768 | 640000 | 626.56 | 150.06 | 4.18x **over** | yes | - |
| `new` | small | 64 | 76800000 | 1.38 | 3.63 | 0.38x | yes | argument-free |
| `new` | medium | 2048 | 76800000 | 1.45 | 3.55 | 0.41x | yes | argument-free |
| `new` | large | 32768 | 134400000 | 1.41 | 3.79 | 0.37x | yes | argument-free |
| `new` | edge-empty | 0 | 70400000 | 1.47 | 3.50 | 0.42x | yes | argument-free |
| `insert` | edge-empty | 0 | 6400000 | 1860.55 | 386.76 | 4.81x **over** | yes | - |
| `lookup` | edge-empty | 0 | 500000 | 185.00 | 1.62 | 114.55x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 600000 | 177.50 | 2.32 | 76.48x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 600000 | 212.50 | 1.76 | 120.57x **over** | yes | barrier-dominated |
| `prefix_entries` | edge-empty | 0 | 6800000 | 26.25 | 4.82 | 5.45x **over** | yes | - |
| `longest_prefix` | edge-empty | 0 | 600000 | 181.67 | 3.38 | 53.68x **over** | yes | - |

### `queue`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `enqueue` | small | 64 | 25600000 | 7.03 | 1.45 | 4.84x **over** | yes | barrier-dominated |
| `enqueue` | medium | 4096 | 19200000 | 7.37 | 1.43 | 5.15x **over** | yes | barrier-dominated |
| `enqueue` | large | 262144 | 17825792 | 7.91 | 1.40 | 5.65x **over** | yes | barrier-dominated |
| `peek` | small | 64 | 76800000 | 1.39 | 1.13 | 1.23x | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 70400000 | 1.53 | 1.20 | 1.27x | yes | argument-free, barrier-dominated |
| `peek` | large | 262144 | 66300000 | 1.40 | 1.12 | 1.24x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 102400000 | 1.09 | 3.18 | 0.34x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.07 | 3.08 | 0.35x | yes | argument-free |
| `length` | large | 262144 | 166400000 | 1.24 | 3.29 | 0.38x | yes | argument-free |
| `to_list` | small | 64 | 240000 | 743.75 | 104.34 | 7.13x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 3000 | 34500.00 | 7276.67 | 4.74x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 2170000.00 | 427770.00 | 5.07x **over** | yes | argument-free |
| `dequeue` | small | 64 | 20400000 | 12.67 | 8.74 | 1.45x | yes | restoring pair |
| `dequeue` | medium | 4096 | 15300000 | 9.41 | 8.30 | 1.13x | yes | restoring pair |
| `dequeue` | large | 262144 | 12750000 | 11.02 | 8.96 | 1.23x | yes | restoring pair |
| `new` | small | 64 | 38400000 | 3.72 | 1.41 | 2.63x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 30600000 | 3.87 | 1.40 | 2.76x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 262144 | 51000000 | 3.71 | 1.38 | 2.68x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 38400000 | 3.88 | 1.42 | 2.73x **over** | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 153600000 | 1.22 | 3.59 | 0.34x | yes | argument-free |
| `enqueue` | edge-empty | 0 | 819200000 | 8.26 | 1.74 | 4.76x **over** | yes | barrier-dominated |
| `dequeue` | edge-empty | 0 | 76800000 | 1.30 | 1.27 | 1.02x | yes | barrier-dominated |
| `peek` | edge-empty | 0 | 64000000 | 1.61 | 1.43 | 1.12x | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 20400000 | 6.86 | 1.46 | 4.70x **over** | yes | argument-free, barrier-dominated |

### `segment_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `range_add` | small | 64 | 1700000 | 57.94 | 36.76 | 1.58x | yes | - |
| `range_add` | medium | 4096 | 1360000 | 134.56 | 77.84 | 1.73x | yes | - |
| `range_add` | large | 262144 | 2720000 | 55.51 | 35.19 | 1.58x | yes | - |
| `get` | small | 64 | 5100000 | 31.27 | 4.12 | 7.59x **over** | yes | - |
| `get` | medium | 4096 | - | FAILED | FAILED | - | - | sample 0: A-B = 185000000ns (bend) / -1881000ns (reference), below the 50000000ns / 100000ns minima |
| `get` | large | 262144 | 8670000 | 77.80 | 14.18 | 5.49x **over** | yes | - |
| `range_query` | small | 64 | 1300000 | 54.62 | 33.73 | 1.62x | yes | - |
| `range_query` | medium | 4096 | 2720000 | 81.43 | 55.18 | 1.48x | yes | - |
| `range_query` | large | 262144 | 5120000 | 25.29 | 17.41 | 1.45x | yes | - |
| `length` | small | 64 | 89600000 | 1.12 | 2.83 | 0.39x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 153600000 | 1.13 | 2.78 | 0.41x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 96000000 | 1.14 | 2.93 | 0.39x | yes | argument-free, barrier-dominated |
| `set` | small | 64 | 3400000 | 53.82 | 13.20 | 4.08x **over** | yes | - |
| `set` | medium | 4096 | 1360000 | 127.21 | 27.78 | 4.58x **over** | yes | - |
| `set` | large | 262144 | 630000 | 200.79 | 128.11 | 1.57x | yes | - |
| `from_list` | small | 64 | 500000 | 286.00 | 81.41 | 3.51x **over** | yes | - |
| `from_list` | medium | 4096 | 600000 | 275.00 | 74.77 | 3.68x **over** | yes | - |
| `from_list` | large | 262144 | 520000 | 284.62 | 84.49 | 3.37x **over** | yes | - |
| `new` | small | 64 | 10200000 | 12.65 | 13.16 | 0.96x | yes | argument-free |
| `new` | medium | 4096 | 10200000 | 12.45 | 13.85 | 0.90x | yes | argument-free |
| `new` | large | 262144 | 6400000 | 13.20 | 13.03 | 1.01x | yes | argument-free |
| `new` | edge-empty | 0 | 12800000 | 12.58 | 13.87 | 0.91x | yes | argument-free |
| `from_list` | edge-empty | 0 | 400000 | 297.50 | 80.19 | 3.71x **over** | yes | - |
| `length` | edge-empty | 0 | 70400000 | 1.33 | 3.42 | 0.39x | yes | argument-free |
| `get` | edge-empty | 0 | 70400000 | 1.48 | 1.43 | 1.04x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 38400000 | 5.04 | 1.46 | 3.46x **over** | yes | barrier-dominated |
| `range_query` | edge-empty | 0 | 12800000 | 10.27 | 2.30 | 4.46x **over** | yes | barrier-dominated |
| `range_add` | edge-empty | 0 | 15300000 | 8.01 | 3.37 | 2.38x | yes | - |

### `union_find`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `find` | small | 64 | 64000000 | 1.83 | 1.57 | 1.17x | yes | barrier-dominated |
| `find` | medium | 4096 | 108800000 | 1.69 | 1.40 | 1.20x | yes | barrier-dominated |
| `find` | large | 65536 | 66560000 | 1.77 | 1.55 | 1.15x | yes | barrier-dominated |
| `union` | small | 64 | 38400000 | 6.17 | 2.08 | 2.97x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 48000000 | 4.65 | 1.65 | 2.81x **over** | yes | barrier-dominated |
| `union` | large | 65536 | - | FAILED | FAILED | - | - | sample 0: A-B = -293000000ns (bend) / 8032000ns (reference), below the 50000000ns / 100000ns minima |
| `connected` | small | 64 | 44800000 | 2.81 | 2.26 | 1.24x | yes | barrier-dominated |
| `connected` | medium | 4096 | 76800000 | 2.43 | 1.81 | 1.34x | yes | barrier-dominated |
| `connected` | large | 65536 | 53760000 | 2.67 | 1.97 | 1.35x | yes | barrier-dominated |
| `component_size` | small | 64 | 57600000 | 2.07 | 1.76 | 1.18x | yes | barrier-dominated |
| `component_size` | medium | 4096 | 67200000 | 1.73 | 1.64 | 1.05x | yes | barrier-dominated |
| `component_size` | large | 65536 | 66560000 | 1.59 | 1.29 | 1.23x | yes | barrier-dominated |
| `component_count` | small | 64 | 102400000 | 1.00 | 2.88 | 0.35x | yes | argument-free, barrier-dominated |
| `component_count` | medium | 4096 | 108800000 | 1.01 | 2.88 | 0.35x | yes | argument-free, barrier-dominated |
| `component_count` | large | 65536 | 166400000 | 1.03 | 2.91 | 0.36x | yes | argument-free, barrier-dominated |
| `new` | small | 64 | 3000000 | 34.50 | 1.92 | 17.97x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 3400000 | 34.12 | 1.87 | 18.23x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 65536 | 3200000 | 34.84 | 1.83 | 19.07x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 5200000 | 35.96 | 1.93 | 18.61x **over** | yes | argument-free, barrier-dominated |
| `find` | edge-empty | 0 | 83200000 | 1.13 | 1.03 | 1.10x | yes | barrier-dominated |
| `union` | edge-empty | 0 | 32000000 | 3.41 | 1.13 | 3.02x **over** | yes | barrier-dominated |
| `connected` | edge-empty | 0 | 64000000 | 1.59 | 1.12 | 1.42x | yes | barrier-dominated |
| `component_size` | edge-empty | 0 | 108800000 | 1.15 | 1.02 | 1.14x | yes | barrier-dominated |
| `component_count` | edge-empty | 0 | 192000000 | 1.02 | 2.88 | 0.35x | yes | argument-free, barrier-dominated |

## Individual samples

Every sample of every measured row, nanoseconds per operation, in the
order taken (Bend and reference alternate within a row):

```
dynamic_array.push                       small        bend 9.31 6.32 7.11 6.91 6.42 7.06
                                                      ref  4.23 4.42 3.77 3.76 3.75 3.98
dynamic_array.push                       medium       bend 6.81 6.67 6.81 6.81 6.86 6.47
                                                      ref  3.80 3.81 5.28 3.76 3.82 3.99
dynamic_array.push                       large        bend 7.21 7.57 9.06 7.51 6.56 6.50
                                                      ref  4.71 4.66 4.36 4.64 4.65 5.98
dynamic_array.get                        small        bend 1.42 1.92 1.97 2.20 2.09 1.84
                                                      ref  1.66 1.63 1.44 1.97 1.66 1.67
dynamic_array.get                        medium       bend 1.84 1.89 1.84 1.81 1.80 2.03
                                                      ref  1.40 1.57 0.93 1.63 1.41 1.54
dynamic_array.get                        large        bend 2.30 2.07 2.07 2.17 2.15 1.98
                                                      ref  1.36 1.51 1.54 1.42 1.33 3.00
dynamic_array.set                        small        bend 1.78 1.78 1.64 1.64 1.70 1.61
                                                      ref  1.56 1.51 1.54 1.53 1.51 1.54
dynamic_array.set                        medium       bend 1.49 1.46 1.89 1.42 1.49 1.43
                                                      ref  1.36 1.38 1.30 1.40 1.38 1.38
dynamic_array.set                        large        bend 1.50 1.44 1.65 2.16 2.01 1.84
                                                      ref  1.46 1.62 2.70 1.78 1.71 1.90
dynamic_array.length                     small        bend 1.12 1.10 1.12 1.09 1.02 1.09
                                                      ref  3.18 3.10 3.15 3.14 3.16 3.13
dynamic_array.length                     medium       bend 1.15 1.07 1.06 1.08 1.10 1.10
                                                      ref  3.25 3.15 2.99 3.19 3.22 3.29
dynamic_array.length                     large        bend 1.38 1.14 1.20 1.25 1.19 1.06
                                                      ref  3.39 3.42 3.42 3.34 3.10 3.24
dynamic_array.capacity                   small        bend 1.08 1.05 1.08 1.05 1.13 1.05
                                                      ref  2.73 2.71 2.72 2.77 2.72 2.76
dynamic_array.capacity                   medium       bend 1.12 1.08 1.03 1.06 1.11 1.09
                                                      ref  2.75 2.74 2.65 2.69 2.64 2.62
dynamic_array.capacity                   large        bend 1.17 1.16 1.18 1.12 1.19 1.15
                                                      ref  3.00 3.16 2.62 3.27 2.86 2.76
dynamic_array.reserve                    small        bend 3.98 4.11 4.43 4.38 4.35 4.58
                                                      ref  1.39 1.43 1.36 1.41 1.33 1.37
dynamic_array.reserve                    medium       bend 3.98 4.22 4.18 4.18 4.18 4.41
                                                      ref  1.35 1.33 1.33 1.33 1.33 1.33
dynamic_array.reserve                    large        bend 4.10 4.22 4.22 4.18 4.18 4.49
                                                      ref  1.43 1.35 1.32 1.33 1.35 1.33
dynamic_array.to_list                    small        bend 580.00 580.00 570.00 610.00 600.00 665.00
                                                      ref  95.91 89.94 92.36 92.61 99.27 90.22
dynamic_array.to_list                    medium       bend 30750.00 33750.00 32500.00 27750.00 30250.00 32750.00
                                                      ref  5525.75 4680.00 4745.50 4913.75 5403.50 5029.75
dynamic_array.to_list                    large        bend 1870000.00 1770000.00 1930000.00 1920000.00 2030000.00 2060000.00
                                                      ref  415320.00 355350.00 390570.00 420760.00 357640.00 365270.00
dynamic_array.clear                      small        bend 56.92 55.77 55.77 56.15 55.77 53.85
                                                      ref  6.93 6.93 6.93 6.91 6.91 7.06
dynamic_array.clear                      medium       bend 3000.00 3025.00 2950.00 3150.00 3075.00 3075.00
                                                      ref  675.15 44.52 414.45 602.08 865.45 789.50
dynamic_array.clear                      large        bend 186000.00 204000.00 204000.00 211000.00 199000.00 220000.00
                                                      ref  14974.00 13897.00 16600.00 14326.00 15519.00 15132.00
dynamic_array.pop                        small        bend 5.20 5.27 5.66 5.35 5.47 4.88
                                                      ref  4.42 3.89 3.08 3.71 4.29 6.21
dynamic_array.pop                        medium       bend 5.23 4.95 5.08 5.99 5.21 5.05
                                                      ref  5.20 3.74 4.21 3.53 3.84 3.36
dynamic_array.pop                        large        bend 5.40 4.92 5.19 5.32 5.23 5.27
                                                      ref  3.48 3.95 4.07 2.99 3.19 2.92
dynamic_array.new                        small        bend 4.06 4.34 3.95 4.53 4.10 4.49
                                                      ref  2.95 2.81 2.94 2.79 2.95 2.85
dynamic_array.new                        medium       bend 4.12 5.16 4.25 4.31 3.99 4.51
                                                      ref  2.99 2.77 3.03 2.96 3.08 2.84
dynamic_array.new                        large        bend 3.99 4.53 4.17 4.53 4.03 4.53
                                                      ref  3.09 2.85 3.13 2.89 3.03 2.80
dynamic_array.new                        edge-empty   bend 4.02 4.30 3.87 4.30 4.14 4.22
                                                      ref  2.96 2.85 2.98 2.89 3.00 2.89
dynamic_array.length                     edge-empty   bend 1.08 1.08 1.08 1.04 1.03 1.06
                                                      ref  2.91 2.90 3.06 2.85 3.06 3.13
dynamic_array.capacity                   edge-empty   bend 1.19 1.17 1.16 1.10 1.07 1.09
                                                      ref  2.71 3.20 2.78 2.69 2.69 2.79
dynamic_array.get                        edge-empty   bend 1.41 1.63 1.48 1.30 1.29 1.29
                                                      ref  1.31 1.39 1.20 1.16 1.17 1.17
dynamic_array.set                        edge-empty   bend 1.27 1.18 1.25 1.19 1.24 1.21
                                                      ref  1.11 1.16 1.13 1.18 1.17 1.20
dynamic_array.push                       edge-empty   bend 6.62 6.23 6.57 6.37 6.37 6.47
                                                      ref  4.13 4.04 3.98 3.75 3.78 3.42
dynamic_array.pop                        edge-empty   bend 1.17 1.10 1.12 1.06 1.15 1.04
                                                      ref  1.11 1.12 1.06 1.13 1.01 1.14
dynamic_array.reserve                    edge-empty   bend 4.01 4.19 4.14 4.22 4.27 4.22
                                                      ref  1.23 1.25 1.25 1.25 1.25 1.26
dynamic_array.clear                      edge-empty   bend 3.69 4.04 3.25 4.38 4.07 4.43
                                                      ref  2.23 2.02 2.21 2.26 2.42 2.18
dynamic_array.to_list                    edge-empty   bend 4.45 5.31 4.65 5.27 5.00 5.04
                                                      ref  2.12 2.05 2.65 2.18 2.23 2.19
deque.push_front                         small        bend 6.69 6.69 6.76 6.76 6.62 7.43
                                                      ref  1.40 1.38 1.40 1.38 1.40 1.38
deque.push_front                         medium       bend 6.30 6.25 5.78 5.89 6.20 6.72
                                                      ref  1.40 1.38 1.40 1.46 1.33 1.40
deque.push_front                         large        bend 6.88 6.84 6.62 7.55 7.11 6.92
                                                      ref  1.38 1.44 1.40 1.43 1.49 1.45
deque.push_back                          small        bend 6.57 6.52 6.42 6.42 6.23 6.23
                                                      ref  1.46 1.47 1.46 1.48 1.46 1.41
deque.push_back                          medium       bend 6.77 7.14 7.08 6.56 6.72 6.67
                                                      ref  1.35 1.44 1.36 1.46 1.34 1.35
deque.push_back                          large        bend 7.85 6.06 6.96 6.66 8.38 5.98
                                                      ref  1.45 1.37 1.41 1.43 1.51 1.55
deque.peek_front                         small        bend 1.13 1.10 1.18 1.07 1.12 1.05
                                                      ref  1.12 1.26 1.12 1.14 1.14 1.11
deque.peek_front                         medium       bend 1.10 1.22 1.24 1.12 1.20 1.35
                                                      ref  1.20 1.24 1.12 1.27 1.13 1.25
deque.peek_front                         large        bend 1.16 1.11 1.20 1.13 1.25 1.10
                                                      ref  1.16 1.24 1.42 1.18 1.15 1.19
deque.peek_back                          small        bend 1.14 1.07 1.18 1.08 1.17 1.07
                                                      ref  1.17 1.16 1.15 1.17 1.10 1.20
deque.peek_back                          medium       bend 1.20 1.06 1.18 1.07 1.26 1.09
                                                      ref  1.11 1.22 1.09 1.30 1.39 1.22
deque.peek_back                          large        bend 1.19 1.07 1.13 1.05 1.15 1.19
                                                      ref  1.13 1.19 1.16 1.18 1.10 1.22
deque.length                             small        bend 1.08 1.05 1.09 1.26 1.10 1.10
                                                      ref  3.06 3.11 3.01 2.94 3.05 3.09
deque.length                             medium       bend 1.09 1.05 1.09 1.07 1.12 1.12
                                                      ref  3.17 3.19 3.17 3.20 3.15 3.09
deque.length                             large        bend 1.08 1.11 1.14 1.05 1.06 1.03
                                                      ref  3.11 3.18 3.15 3.13 3.18 3.08
deque.to_list                            small        bend 590.00 655.00 605.00 680.00 655.00 645.00
                                                      ref  89.21 89.45 95.07 84.03 95.07 90.18
deque.to_list                            medium       bend 31750.00 31500.00 31000.00 30500.00 29250.00 30250.00
                                                      ref  6928.00 6329.75 6572.75 6266.25 6501.00 6182.00
deque.to_list                            large        bend 1880000.00 1930000.00 2160000.00 2090000.00 1960000.00 2630000.00
                                                      ref  402120.00 398210.00 413910.00 384520.00 382840.00 415900.00
deque.pop_front                          small        bend 4.85 5.29 4.41 4.66 4.31 4.75
                                                      ref  9.26 7.45 7.61 7.10 8.06 6.98
deque.pop_front                          medium       bend 4.38 4.88 5.00 5.08 4.34 4.80
                                                      ref  7.39 7.29 7.79 7.06 8.13 6.91
deque.pop_front                          large        bend 4.35 4.75 4.35 4.82 4.47 4.78
                                                      ref  8.01 7.13 7.99 7.13 7.61 6.89
deque.pop_back                           small        bend 4.45 4.96 4.65 5.04 4.41 4.80
                                                      ref  7.57 6.78 7.74 6.64 7.64 6.94
deque.pop_back                           medium       bend 4.45 4.92 4.38 4.96 4.45 5.12
                                                      ref  7.86 6.97 7.56 6.80 7.53 6.70
deque.pop_back                           large        bend 4.34 5.08 4.36 4.88 3.86 5.62
                                                      ref  7.20 6.51 7.44 6.48 8.89 6.61
deque.new                                small        bend 3.28 3.39 3.67 3.28 3.80 3.70
                                                      ref  1.31 1.29 1.31 1.43 1.44 1.41
deque.new                                medium       bend 3.14 3.40 3.30 3.30 3.33 4.15
                                                      ref  1.50 1.32 1.36 1.32 1.31 1.36
deque.new                                large        bend 3.47 3.32 3.52 3.38 3.24 3.32
                                                      ref  1.34 1.32 1.33 1.31 1.45 1.31
deque.new                                edge-empty   bend 3.12 3.83 3.05 3.62 3.62 3.20
                                                      ref  1.32 1.30 1.33 1.31 1.31 1.35
deque.length                             edge-empty   bend 1.10 1.12 1.37 1.10 1.10 1.08
                                                      ref  3.22 3.45 3.51 3.20 3.20 3.16
deque.push_front                         edge-empty   bend 6.18 7.21 7.16 7.79 7.11 6.91
                                                      ref  1.42 1.40 1.39 1.55 1.39 1.39
deque.push_back                          edge-empty   bend 6.56 6.60 6.88 6.64 6.45 6.56
                                                      ref  1.35 1.44 1.37 1.47 1.42 1.47
deque.pop_front                          edge-empty   bend 1.16 1.12 1.10 1.10 1.12 1.09
                                                      ref  1.10 1.11 1.12 1.11 1.12 1.11
deque.pop_back                           edge-empty   bend 1.13 1.03 1.07 1.22 1.22 1.25
                                                      ref  1.09 1.12 1.14 1.21 1.30 1.26
deque.peek_front                         edge-empty   bend 1.22 1.16 1.18 1.12 1.19 1.09
                                                      ref  1.16 1.17 1.17 1.16 1.10 1.13
deque.peek_back                          edge-empty   bend 1.13 1.07 1.14 1.14 1.23 1.08
                                                      ref  1.08 1.16 1.09 1.34 1.12 1.20
deque.to_list                            edge-empty   bend 6.37 6.23 6.37 6.47 6.32 6.27
                                                      ref  1.23 1.29 1.22 1.30 1.30 1.30
queue.enqueue                            small        bend 7.03 7.03 7.07 7.15 6.25 6.95
                                                      ref  1.42 1.46 1.31 1.45 1.47 1.45
queue.enqueue                            medium       bend 7.29 7.76 6.88 7.71 7.03 7.45
                                                      ref  1.46 1.43 1.40 1.43 1.45 1.43
queue.enqueue                            large        bend 8.36 8.25 7.52 8.13 7.69 7.18
                                                      ref  1.50 1.48 1.51 1.32 1.27 1.32
queue.peek                               small        bend 1.41 1.39 1.39 1.30 1.28 1.41
                                                      ref  1.11 1.12 1.13 1.13 1.22 1.37
queue.peek                               medium       bend 1.58 1.62 1.51 1.49 1.56 1.39
                                                      ref  1.24 1.21 1.23 1.20 1.13 1.17
queue.peek                               large        bend 1.51 1.33 1.37 1.39 1.42 1.40
                                                      ref  1.13 1.20 1.12 1.13 1.12 1.11
queue.length                             small        bend 1.12 1.05 1.12 1.07 1.11 1.07
                                                      ref  3.18 3.24 3.20 3.18 3.11 3.08
queue.length                             medium       bend 1.07 1.06 1.07 1.11 1.11 1.07
                                                      ref  3.06 3.06 3.16 3.10 3.06 3.13
queue.length                             large        bend 1.04 1.06 1.27 1.29 1.22 1.55
                                                      ref  3.12 3.07 3.15 3.43 3.93 3.94
queue.to_list                            small        bend 891.67 758.33 712.50 783.33 729.17 716.67
                                                      ref  113.22 104.08 110.12 104.22 100.37 104.46
queue.to_list                            medium       bend 32666.67 32666.67 23333.33 39000.00 36333.33 40333.33
                                                      ref  6915.33 6669.33 8049.00 7890.00 7305.33 7248.00
queue.to_list                            large        bend 2120000.00 2240000.00 2400000.00 2180000.00 2160000.00 2120000.00
                                                      ref  595900.00 464840.00 423000.00 430520.00 425020.00 413820.00
queue.dequeue                            small        bend 13.33 11.47 14.17 12.01 15.15 9.56
                                                      ref  9.35 8.31 9.56 7.84 9.15 8.33
queue.dequeue                            medium       bend 11.11 8.24 11.05 8.37 10.33 8.50
                                                      ref  8.29 7.76 9.63 8.32 9.07 7.88
queue.dequeue                            large        bend 12.08 9.96 13.33 8.78 19.06 9.88
                                                      ref  9.58 8.02 9.61 8.43 9.50 8.13
queue.new                                small        bend 3.62 3.83 3.54 4.06 3.46 4.27
                                                      ref  1.44 1.41 1.47 1.42 1.41 1.41
queue.new                                medium       bend 3.53 3.79 3.95 3.56 4.18 4.28
                                                      ref  1.39 1.41 1.40 1.41 1.40 1.29
queue.new                                large        bend 3.51 3.76 3.47 3.65 4.08 4.80
                                                      ref  1.33 1.46 1.51 1.29 1.30 1.44
queue.new                                edge-empty   bend 4.22 4.14 4.14 3.62 3.59 3.57
                                                      ref  1.43 1.43 1.36 1.42 1.35 1.42
queue.length                             edge-empty   bend 1.07 1.41 1.41 1.17 1.24 1.21
                                                      ref  3.05 3.92 3.76 3.40 3.43 3.81
queue.enqueue                            edge-empty   bend 6.41 8.54 7.62 8.19 8.33 8.60
                                                      ref  1.72 1.53 1.52 1.81 2.58 1.75
queue.dequeue                            edge-empty   bend 1.33 1.26 1.26 1.24 1.38 1.48
                                                      ref  1.22 1.37 1.26 1.39 1.27 1.14
queue.peek                               edge-empty   bend 1.62 1.56 1.59 1.48 1.80 2.06
                                                      ref  1.43 1.39 1.28 1.44 1.56 1.44
queue.to_list                            edge-empty   bend 6.86 6.86 6.67 7.35 6.86 7.35
                                                      ref  1.48 1.27 1.42 1.50 1.53 1.45
doubly_linked_list.push_front            small        bend 5640.00 5310.00 5170.00 5590.00 6170.00 6500.00
                                                      ref  328.01 300.54 328.28 341.62 332.42 387.83
doubly_linked_list.push_front            medium       bend 5340.00 5300.00 5080.00 7280.00 5460.00 5180.00
                                                      ref  262.42 272.28 262.60 305.50 286.54 322.84
doubly_linked_list.push_front            large        bend 6011.96 5340.58 5340.58 5218.51 3540.04 6256.10
                                                      ref  250.76 309.14 240.63 282.47 263.15 312.62
doubly_linked_list.push_back             small        bend 6140.00 5220.00 5290.00 5480.00 5290.00 5110.00
                                                      ref  316.47 300.79 284.05 349.31 313.48 351.93
doubly_linked_list.push_back             medium       bend 5820.00 6040.00 7080.00 5780.00 4960.00 4920.00
                                                      ref  294.24 288.48 271.36 304.42 271.72 243.00
doubly_linked_list.insert_before         small        bend 8190.00 8090.00 9280.00 9090.00 9800.00 8340.00
                                                      ref  505.47 514.41 505.87 509.57 487.79 417.72
doubly_linked_list.insert_before         medium       bend 6660.00 7520.00 6400.00 7380.00 6660.00 8180.00
                                                      ref  462.60 426.52 442.90 447.66 432.90 454.64
doubly_linked_list.insert_before         large        bend 7550.00 8700.00 6950.00 9050.00 7000.00 7750.00
                                                      ref  534.10 633.65 574.45 642.55 677.60 664.15
doubly_linked_list.insert_after          small        bend 8030.00 7570.00 7480.00 7520.00 7270.00 7320.00
                                                      ref  540.40 526.52 523.31 570.31 488.97 541.07
doubly_linked_list.insert_after          medium       bend 7280.00 7820.00 8780.00 7980.00 7140.00 7680.00
                                                      ref  517.22 532.28 489.46 554.40 506.98 506.62
doubly_linked_list.insert_after          large        bend 6800.00 8800.00 7250.00 10150.00 7150.00 9550.00
                                                      ref  691.85 663.75 807.75 598.50 763.40 621.40
doubly_linked_list.get                   small        bend 205.00 266.67 213.33 223.33 203.33 196.67
                                                      ref  30.42 28.53 29.83 28.11 27.07 25.81
doubly_linked_list.get                   medium       bend 400.00 560.00 493.33 426.67 390.00 570.00
                                                      ref  61.16 62.82 58.94 57.33 59.56 63.44
doubly_linked_list.get                   large        bend 725.00 614.29 678.57 639.29 617.86 617.86
                                                      ref  163.56 148.32 136.60 119.10 158.41 118.97
doubly_linked_list.set                   small        bend 715.00 690.00 725.00 710.00 700.00 705.00
                                                      ref  23.75 24.84 28.42 27.00 27.97 26.11
doubly_linked_list.set                   medium       bend 1340.00 1430.00 1460.00 1420.00 1390.00 1680.00
                                                      ref  54.51 52.24 54.30 53.63 55.17 54.36
doubly_linked_list.set                   large        bend 2375.78 2203.91 2255.47 1979.69 1807.03 2276.56
                                                      ref  146.93 132.74 145.92 133.91 151.90 150.69
doubly_linked_list.next                  small        bend 185.00 202.00 185.00 180.00 163.00 196.00
                                                      ref  23.74 26.60 23.68 22.74 27.57 25.34
doubly_linked_list.next                  medium       bend 348.12 397.19 344.38 454.06 431.88 365.94
                                                      ref  49.32 39.27 49.25 52.38 48.93 44.71
doubly_linked_list.next                  large        bend 433.33 246.67 623.33 533.33 533.33 503.33
                                                      ref  145.96 156.47 141.76 146.17 148.68 134.19
doubly_linked_list.prev                  small        bend 175.00 176.67 163.33 171.67 175.00 171.67
                                                      ref  24.70 22.46 24.14 24.59 24.79 23.32
doubly_linked_list.prev                  medium       bend 330.00 356.67 340.00 330.00 313.33 330.00
                                                      ref  48.26 48.01 48.80 46.31 47.31 47.08
doubly_linked_list.prev                  large        bend 513.89 425.00 555.56 433.33 547.22 538.89
                                                      ref  159.30 136.32 144.33 150.46 151.03 130.91
doubly_linked_list.length                small        bend 5.82 7.11 5.39 4.77 4.65 4.41
                                                      ref  4.39 3.31 3.25 3.37 3.08 2.96
doubly_linked_list.length                medium       bend 2.07 4.73 4.14 4.96 4.30 4.84
                                                      ref  3.43 2.73 3.49 3.02 3.05 3.24
doubly_linked_list.length                large        bend 4.63 4.96 4.75 4.81 3.34 5.02
                                                      ref  3.34 2.96 3.29 2.84 3.05 3.34
doubly_linked_list.to_list               small        bend 14000.00 14300.00 14000.00 13000.00 13800.00 12900.00
                                                      ref  269.30 278.50 304.70 233.30 257.00 176.60
doubly_linked_list.to_list               medium       bend 676666.67 846666.67 956666.67 890000.00 803333.33 970000.00
                                                      ref  25953.33 22513.33 24673.33 20470.00 19926.67 21633.33
doubly_linked_list.to_list               large        bend 19600000.00 16950000.00 13700000.00 22150000.00 16000000.00 27650000.00
                                                      ref  1482550.00 1148250.00 1130800.00 1193250.00 79950.00 1311400.00
doubly_linked_list.remove                medium       bend 1924.40 1737.71 1881.32 1306.87 1881.32 1651.54
                                                      ref  113.93 54.03 118.35 65.37 135.12 105.78
doubly_linked_list.remove                large        bend 1790.36 2441.41 2827.96 2644.86 2400.72 3072.10
                                                      ref  230.43 263.90 204.83 190.29 298.46 219.36
doubly_linked_list.new                   small        bend 1.11 1.13 1.23 1.23 1.20 1.38
                                                      ref  2.79 3.61 3.10 3.08 3.14 3.01
doubly_linked_list.new                   medium       bend 1.46 1.36 1.16 1.17 1.15 1.13
                                                      ref  3.04 2.98 2.88 2.96 3.37 2.84
doubly_linked_list.new                   large        bend 1.30 1.32 1.20 1.15 1.00 1.27
                                                      ref  3.12 2.83 2.94 2.86 3.29 2.87
doubly_linked_list.new                   edge-empty   bend 1.17 1.11 1.02 1.03 1.08 1.07
                                                      ref  2.88 2.65 2.65 2.73 2.60 2.83
doubly_linked_list.length                edge-empty   bend 1.10 0.94 1.09 1.36 1.11 1.14
                                                      ref  2.82 2.76 2.76 2.82 2.98 2.66
doubly_linked_list.push_front            edge-empty   bend 5330.00 5170.00 5320.00 5690.00 8710.00 7970.00
                                                      ref  315.47 319.46 288.32 331.16 296.69 317.48
doubly_linked_list.push_back             edge-empty   bend 6750.00 4690.00 4550.00 4860.00 4740.00 4590.00
                                                      ref  272.49 274.10 254.10 273.70 290.06 285.91
doubly_linked_list.insert_before         edge-empty   bend 10.23 12.66 12.66 11.25 11.33 10.94
                                                      ref  1.30 1.91 1.43 1.30 1.30 1.21
doubly_linked_list.insert_after          edge-empty   bend 10.78 11.09 12.97 11.41 11.09 11.09
                                                      ref  1.22 1.31 1.30 1.18 1.35 1.21
doubly_linked_list.remove                edge-empty   bend 9.38 9.61 9.38 10.16 9.53 9.92
                                                      ref  1.22 1.22 1.22 1.30 1.30 1.20
doubly_linked_list.get                   edge-empty   bend 10.20 9.54 11.11 10.59 11.44 9.87
                                                      ref  1.30 1.20 1.33 1.26 1.30 1.19
doubly_linked_list.set                   edge-empty   bend 9.92 10.16 9.69 9.84 10.00 9.92
                                                      ref  1.27 1.14 1.22 1.22 1.24 1.11
doubly_linked_list.next                  edge-empty   bend 4.65 4.61 4.38 4.77 4.41 4.49
                                                      ref  1.25 1.22 1.24 1.21 1.22 1.20
doubly_linked_list.prev                  edge-empty   bend 4.65 4.80 4.34 4.69 5.08 4.57
                                                      ref  1.35 1.11 1.22 1.18 1.30 2.06
doubly_linked_list.to_list               edge-empty   bend 7.71 8.33 8.02 11.09 7.29 8.28
                                                      ref  4.59 4.30 4.78 3.71 4.56 4.05
binary_heap.push                         small        bend 20.78 19.12 20.29 21.86 20.88 21.67
                                                      ref  12.77 11.56 12.82 13.71 14.50 13.87
binary_heap.push                         medium       bend 23.73 20.39 22.16 19.41 18.43 19.80
                                                      ref  13.75 11.43 13.08 11.22 11.62 12.02
binary_heap.push                         large        bend 20.64 24.38 23.04 16.16 20.05 17.50
                                                      ref  10.78 10.74 11.95 11.51 5.09 10.80
binary_heap.peek                         small        bend 1.16 1.15 1.17 1.09 1.17 1.10
                                                      ref  1.18 1.22 1.15 1.18 1.09 1.19
binary_heap.peek                         medium       bend 1.18 1.24 1.15 1.14 1.26 1.07
                                                      ref  1.24 1.23 1.17 1.20 1.24 1.21
binary_heap.peek                         large        bend 1.19 1.04 1.09 1.15 1.17 1.11
                                                      ref  1.07 1.13 1.14 1.21 1.13 1.20
binary_heap.length                       small        bend 1.17 1.23 1.36 1.26 1.35 0.78
                                                      ref  3.38 3.77 4.90 3.47 2.60 4.24
binary_heap.length                       medium       bend 1.03 1.11 1.07 1.11 1.10 1.07
                                                      ref  3.01 3.05 3.18 2.99 3.03 3.13
binary_heap.length                       large        bend 1.07 1.08 1.06 1.12 1.09 1.30
                                                      ref  3.08 3.07 2.91 3.49 3.92 3.17
binary_heap.from_list                    small        bend 132.38 139.05 120.00 144.76 137.14 131.43
                                                      ref  67.29 58.59 116.17 57.63 70.19 56.43
binary_heap.from_list                    medium       bend 121.18 144.71 136.47 137.65 134.12 145.88
                                                      ref  72.55 58.90 70.88 55.57 97.14 64.90
binary_heap.from_list                    large        bend 155.77 137.50 131.73 130.77 125.96 141.35
                                                      ref  68.03 54.86 69.74 60.52 90.03 70.13
binary_heap.to_sorted_list               small        bend 1382.35 1509.80 1343.14 1401.96 1392.16 1352.94
                                                      ref  656.35 597.57 607.68 606.33 661.53 597.23
binary_heap.to_sorted_list               medium       bend 112857.14 184285.71 164285.71 172857.14 147142.86 174285.71
                                                      ref  103650.00 77898.57 78447.14 70135.71 82717.14 73211.43
binary_heap.to_sorted_list               large        bend 11666666.67 9400000.00 10333333.33 10200000.00 10666666.67 9400000.00
                                                      ref  4343933.33 3844533.33 4086066.67 4811733.33 4321266.67 4327666.67
binary_heap.pop                          small        bend 42.06 40.59 40.59 40.29 43.82 40.88
                                                      ref  19.13 17.86 15.66 18.14 16.84 11.40
binary_heap.pop                          medium       bend 84.29 79.52 81.90 81.43 85.24 90.48
                                                      ref  33.00 37.09 35.82 37.07 36.53 37.31
binary_heap.pop                          large        bend 138.24 138.24 135.29 139.22 137.25 133.33
                                                      ref  53.22 55.46 51.48 52.58 51.74 53.07
binary_heap.new                          small        bend 4.19 3.63 2.97 3.31 2.87 3.24
                                                      ref  3.53 2.75 3.10 2.75 3.08 2.81
binary_heap.new                          medium       bend 2.68 3.31 3.31 3.96 2.63 3.28
                                                      ref  3.05 2.81 3.17 2.74 3.10 2.73
binary_heap.new                          large        bend 3.48 3.31 2.84 3.38 2.83 4.19
                                                      ref  2.85 2.67 3.09 2.69 3.16 3.16
binary_heap.new                          edge-empty   bend 3.12 3.28 2.69 3.59 2.84 3.62
                                                      ref  3.47 2.74 3.18 2.82 4.32 3.14
binary_heap.length                       edge-empty   bend 1.10 1.07 1.03 1.15 1.09 1.24
                                                      ref  3.29 3.03 3.20 3.09 3.21 3.17
binary_heap.push                         edge-empty   bend 18.82 19.41 19.12 15.15 17.94 16.47
                                                      ref  12.17 12.98 11.22 11.92 12.52 12.30
binary_heap.peek                         edge-empty   bend 1.21 1.11 1.19 1.09 1.13 1.11
                                                      ref  1.14 1.32 1.08 1.14 1.11 1.12
binary_heap.pop                          edge-empty   bend 1.15 1.06 1.15 1.18 1.20 1.00
                                                      ref  1.10 1.20 1.16 1.27 1.16 1.19
binary_heap.from_list                    edge-empty   bend 123.33 132.22 125.56 133.33 121.11 125.56
                                                      ref  63.98 54.89 65.88 60.37 69.44 54.56
binary_heap.to_sorted_list               edge-empty   bend 10.78 11.09 10.08 11.72 10.47 11.25
                                                      ref  5.28 5.05 5.32 4.98 4.84 5.22
balanced_search_tree.insert              small        bend 426.67 386.67 426.67 426.67 410.00 416.67
                                                      ref  32.64 28.03 30.38 27.90 30.63 29.94
balanced_search_tree.insert              medium       bend 1224.00 1116.00 1200.00 1092.00 1072.00 1236.00
                                                      ref  88.07 83.89 81.29 76.64 76.98 75.88
balanced_search_tree.insert              large        bend 1700.00 1850.00 920.00 2050.00 1740.00 1850.00
                                                      ref  193.81 177.90 186.09 185.35 195.94 212.64
balanced_search_tree.remove              small        bend 935.00 910.00 945.00 865.00 880.00 880.00
                                                      ref  72.92 61.64 71.42 72.41 66.86 75.11
balanced_search_tree.remove              medium       bend 1930.00 2000.00 1940.00 2010.00 1960.00 1660.00
                                                      ref  157.14 153.17 155.22 154.28 158.36 150.52
balanced_search_tree.remove              large        bend 2687.50 2500.00 2275.00 2875.00 2637.50 1875.00
                                                      ref  265.51 270.66 275.45 283.59 292.43 287.54
balanced_search_tree.lookup              small        bend 132.14 142.86 140.71 132.14 140.00 132.14
                                                      ref  20.15 19.56 19.92 19.97 19.64 19.21
balanced_search_tree.lookup              medium       bend 302.50 292.50 292.50 302.50 287.50 290.00
                                                      ref  46.52 48.11 45.62 42.39 46.51 43.53
balanced_search_tree.lookup              large        bend 490.00 575.00 675.00 515.00 540.00 330.00
                                                      ref  107.36 101.76 103.06 131.47 114.00 102.70
balanced_search_tree.contains            small        bend 142.86 140.71 145.00 130.71 141.43 142.14
                                                      ref  21.36 18.96 22.35 20.71 23.11 19.96
balanced_search_tree.contains            medium       bend 302.50 317.50 300.00 302.50 290.00 325.00
                                                      ref  47.12 45.63 48.05 46.62 50.75 50.47
balanced_search_tree.contains            large        bend 523.81 542.86 480.95 811.90 611.90 552.38
                                                      ref  111.28 104.77 121.71 110.34 121.38 102.31
balanced_search_tree.min                 small        bend 38.67 43.67 41.67 40.33 51.33 46.33
                                                      ref  1.27 1.28 1.31 1.22 1.39 1.41
balanced_search_tree.min                 medium       bend 133.75 141.25 138.75 156.25 113.75 140.00
                                                      ref  6.01 5.11 5.57 4.61 4.57 5.29
balanced_search_tree.min                 large        bend 142.67 164.00 162.00 155.33 155.33 156.67
                                                      ref  6.20 5.83 6.83 5.69 6.38 4.50
balanced_search_tree.max                 small        bend 48.25 50.75 55.25 45.75 50.00 49.50
                                                      ref  1.21 1.22 1.31 1.24 1.52 1.23
balanced_search_tree.max                 medium       bend 131.11 127.78 134.44 158.89 150.00 132.22
                                                      ref  4.32 4.17 4.58 4.91 4.43 4.49
balanced_search_tree.max                 large        bend 182.81 193.12 169.06 175.94 188.75 172.81
                                                      ref  6.01 5.48 6.56 4.59 5.70 5.09
balanced_search_tree.lower_bound         small        bend 142.50 132.50 131.25 131.25 157.50 143.75
                                                      ref  20.55 20.07 20.43 19.40 22.58 19.82
balanced_search_tree.lower_bound         medium       bend 316.67 298.33 291.67 306.67 333.33 311.67
                                                      ref  51.51 46.37 50.27 46.45 45.02 44.91
balanced_search_tree.lower_bound         large        bend 516.18 492.65 477.94 470.59 455.88 501.47
                                                      ref  101.09 100.36 105.77 97.15 112.79 88.12
balanced_search_tree.range               small        bend 271.48 246.09 248.05 251.95 251.95 238.28
                                                      ref  39.08 36.71 38.80 36.14 43.97 43.04
balanced_search_tree.range               medium       bend 14047.62 12142.86 11190.48 13888.89 11507.94 11587.30
                                                      ref  1173.02 917.86 1043.41 1029.68 989.92 949.13
balanced_search_tree.range               large        bend 158593.75 113281.25 150000.00 199218.75 189843.75 153125.00
                                                      ref  9133.59 9102.34 8729.69 6602.34 9896.88 11478.91
balanced_search_tree.to_list             small        bend 816.41 789.06 757.81 875.00 1105.47 769.53
                                                      ref  60.31 63.09 70.46 57.67 59.41 63.97
balanced_search_tree.to_list             medium       bend 74000.00 76666.67 78666.67 77333.33 90666.67 78000.00
                                                      ref  4830.00 14571.33 6429.33 4402.67 4830.00 4636.67
balanced_search_tree.to_list             large        bend 3853333.33 2740000.00 2736666.67 2323333.33 2416666.67 2386666.67
                                                      ref  257136.67 195073.33 89810.00 277323.33 275473.33 230656.67
balanced_search_tree.length              small        bend 1.24 1.09 1.09 1.17 1.06 1.05
                                                      ref  3.07 3.27 3.95 3.08 3.14 3.19
balanced_search_tree.length              medium       bend 1.11 1.16 1.18 1.04 1.10 1.09
                                                      ref  3.22 3.36 3.18 3.13 3.15 3.15
balanced_search_tree.length              large        bend 1.07 1.58 1.02 1.05 1.17 1.07
                                                      ref  3.22 2.98 3.25 3.67 3.83 3.25
balanced_search_tree.new                 small        bend 1.13 1.09 1.09 1.10 1.09 1.10
                                                      ref  2.88 2.77 2.87 2.68 2.78 2.76
balanced_search_tree.new                 medium       bend 1.17 1.10 1.03 1.08 1.08 1.11
                                                      ref  2.78 2.76 2.77 2.77 2.77 3.10
balanced_search_tree.new                 large        bend 1.04 1.29 1.36 1.51 1.53 1.04
                                                      ref  2.82 3.60 3.17 3.36 3.04 2.95
balanced_search_tree.new                 edge-empty   bend 1.18 1.32 1.24 1.20 1.36 1.24
                                                      ref  2.85 2.99 3.06 3.42 3.22 3.35
balanced_search_tree.length              edge-empty   bend 1.17 1.25 1.22 1.23 1.17 1.16
                                                      ref  3.46 3.82 3.42 3.31 3.50 3.40
balanced_search_tree.insert              edge-empty   bend 39.41 55.88 43.24 46.76 40.59 42.06
                                                      ref  3.37 3.71 3.36 3.36 3.40 3.40
balanced_search_tree.remove              edge-empty   bend 7.14 7.45 6.82 7.45 6.93 7.14
                                                      ref  3.24 3.15 3.13 2.97 2.97 2.99
balanced_search_tree.lookup              edge-empty   bend 4.69 4.69 2.66 5.00 4.65 4.84
                                                      ref  1.48 1.35 1.68 1.50 1.42 1.44
balanced_search_tree.contains            edge-empty   bend 4.65 3.55 4.73 4.65 4.26 4.34
                                                      ref  1.44 1.37 1.39 1.30 1.30 1.29
balanced_search_tree.min                 edge-empty   bend 3.94 4.41 3.66 4.28 4.62 3.94
                                                      ref  1.22 1.30 1.34 1.36 1.42 1.22
balanced_search_tree.max                 edge-empty   bend 4.34 4.36 4.12 4.26 4.30 4.18
                                                      ref  1.22 1.30 1.71 1.30 1.24 1.21
balanced_search_tree.lower_bound         edge-empty   bend 5.99 6.46 6.20 6.25 7.24 6.25
                                                      ref  1.32 1.28 1.30 1.31 1.30 1.30
balanced_search_tree.range               edge-empty   bend 4.75 5.34 4.95 5.78 5.15 6.76
                                                      ref  5.44 4.74 5.27 5.10 5.83 5.16
balanced_search_tree.to_list             edge-empty   bend 4.84 8.67 5.31 5.27 5.00 5.16
                                                      ref  4.14 3.83 4.79 3.81 4.20 3.90
bitset.set                               small        bend 2.04 2.21 1.69 1.76 1.77 1.77
                                                      ref  1.70 1.63 1.55 1.66 1.50 1.65
bitset.set                               medium       bend 1.63 1.56 1.53 1.48 1.52 1.49
                                                      ref  1.37 1.40 1.37 1.39 1.40 1.42
bitset.set                               large        bend 1.55 1.44 1.55 1.50 1.53 1.47
                                                      ref  1.39 1.38 1.33 1.39 1.37 1.37
bitset.clear                             small        bend 1.69 1.61 1.61 1.59 1.84 1.66
                                                      ref  1.50 1.60 1.55 0.86 1.56 1.61
bitset.clear                             medium       bend 1.48 1.51 1.53 1.51 1.53 1.51
                                                      ref  1.36 1.34 1.31 1.41 1.37 1.38
bitset.clear                             large        bend 1.58 1.47 1.64 1.80 1.95 1.55
                                                      ref  1.33 1.66 1.24 1.76 1.48 1.50
bitset.get                               small        bend 1.98 1.80 2.03 1.94 2.09 1.86
                                                      ref  1.52 1.73 1.73 1.78 1.61 1.61
bitset.get                               medium       bend 1.83 1.73 1.73 1.72 1.73 1.92
                                                      ref  1.38 1.40 1.38 1.39 1.38 1.44
bitset.get                               large        bend 1.75 1.67 1.73 1.59 1.72 1.71
                                                      ref  1.40 1.38 1.32 1.42 1.29 1.30
bitset.count                             small        bend 60.00 61.18 59.41 60.00 60.59 59.41
                                                      ref  4.73 4.77 4.75 4.75 4.74 5.29
bitset.count                             medium       bend 3425.00 3800.00 3600.00 3650.00 3550.00 3725.00
                                                      ref  240.32 255.25 215.00 232.75 226.30 216.90
bitset.count                             large        bend 218000.00 222000.00 228000.00 270000.00 250000.00 224000.00
                                                      ref  15538.00 14440.00 14450.00 15392.00 14450.00 14438.00
bitset.length                            small        bend 1.07 1.03 1.06 1.05 1.06 1.03
                                                      ref  2.96 3.05 2.93 3.07 2.99 3.09
bitset.length                            medium       bend 1.24 1.17 1.14 1.06 1.07 1.11
                                                      ref  3.09 3.27 3.12 3.05 3.23 3.07
bitset.length                            large        bend 1.11 1.10 1.08 1.06 1.08 1.22
                                                      ref  3.34 3.15 3.08 3.11 3.14 3.51
bitset.to_list                           small        bend 370.00 366.67 340.00 370.00 350.00 406.67
                                                      ref  78.79 75.28 79.14 74.01 80.28 88.14
bitset.to_list                           medium       bend 22333.33 22000.00 20166.67 20666.67 20666.67 21500.00
                                                      ref  5327.17 5000.67 4928.00 4466.67 5121.67 4934.33
bitset.to_list                           large        bend 2040000.00 2050000.00 2150000.00 2170000.00 1980000.00 2490000.00
                                                      ref  346290.00 364780.00 337190.00 313400.00 335940.00 349800.00
bitset.union                             small        bend 7.06 8.25 7.00 6.12 6.88 6.81
                                                      ref  1.45 1.51 1.31 1.44 1.65 1.48
bitset.union                             medium       bend 92.65 82.84 83.82 64.71 69.12 67.65
                                                      ref  72.81 68.96 69.25 63.08 62.40 59.55
bitset.union                             large        bend 3382.35 3558.82 3558.82 3470.59 3441.18 3764.71
                                                      ref  4608.15 4218.15 3777.41 3764.24 4678.06 4531.26
bitset.intersection                      small        bend 8.94 6.44 9.56 6.44 7.25 6.69
                                                      ref  1.61 1.72 1.69 2.05 1.41 1.40
bitset.intersection                      medium       bend 76.47 78.43 51.96 94.61 80.39 71.57
                                                      ref  87.65 68.62 84.51 72.84 65.58 58.21
bitset.intersection                      large        bend 2901.96 3705.88 3549.02 3941.18 3843.14 3294.12
                                                      ref  4514.25 3747.37 3713.98 4675.18 5157.75 3820.96
bitset.difference                        medium       bend 68.63 64.22 64.22 67.65 69.12 84.31
                                                      ref  64.13 58.69 64.13 61.80 57.68 56.07
bitset.difference                        large        bend 3343.75 3531.25 3687.50 3562.50 3906.25 4125.00
                                                      ref  4797.12 3774.41 3789.59 3785.91 4105.06 4188.09
bitset.xor                               small        bend 8.50 6.38 7.38 7.00 6.25 6.56
                                                      ref  2.05 1.49 1.29 1.45 1.44 1.49
bitset.xor                               large        bend 5254.90 4058.82 3666.67 3235.29 3313.73 5588.24
                                                      ref  3523.86 4171.22 4032.12 3393.98 3489.20 3526.08
bitset.new                               small        bend 3.57 3.88 2.89 1.74 3.28 3.80
                                                      ref  12.89 10.59 11.43 13.53 12.85 10.27
bitset.new                               medium       bend 2.89 3.36 3.05 3.85 3.70 3.33
                                                      ref  12.93 9.88 11.42 11.94 12.01 12.58
bitset.new                               large        bend 3.16 3.68 3.23 3.78 4.62 3.30
                                                      ref  11.52 9.53 8.96 12.34 12.86 11.38
bitset.new                               edge-empty   bend 3.24 3.21 3.21 3.82 3.38 1.96
                                                      ref  15.17 11.23 12.54 11.90 9.18 13.65
bitset.length                            edge-empty   bend 1.31 1.18 1.29 1.24 1.26 1.14
                                                      ref  3.36 3.44 3.28 3.41 3.72 3.18
bitset.get                               edge-empty   bend 1.31 1.28 0.70 1.74 1.57 1.33
                                                      ref  1.13 1.33 1.59 1.46 1.30 1.25
bitset.set                               edge-empty   bend 1.38 1.28 0.65 1.47 1.83 2.43
                                                      ref  1.15 1.23 1.18 1.34 1.39 1.01
bitset.clear                             edge-empty   bend 1.55 1.56 1.45 1.60 1.38 1.48
                                                      ref  1.14 1.26 1.24 1.38 1.42 1.30
bitset.count                             edge-empty   bend 46.15 36.54 25.38 37.50 40.38 46.73
                                                      ref  4.33 4.16 4.61 4.65 4.92 4.78
bitset.union                             edge-empty   bend 5.90 7.50 8.01 5.78 5.62 6.05
                                                      ref  1.48 1.04 1.52 1.59 1.43 1.41
bitset.intersection                      edge-empty   bend 5.78 5.72 4.77 5.56 5.56 5.03
                                                      ref  1.40 1.30 1.12 1.27 1.21 1.30
bitset.difference                        edge-empty   bend 5.49 5.64 5.83 5.44 5.88 5.69
                                                      ref  1.37 1.44 1.40 1.37 1.47 1.46
bitset.xor                               edge-empty   bend 5.20 5.70 4.34 9.26 12.62 14.10
                                                      ref  1.22 1.28 1.64 2.37 1.66 1.59
bitset.to_list                           edge-empty   bend 36.75 38.00 38.00 44.50 40.75 43.25
                                                      ref  3.99 3.78 4.65 4.53 4.53 4.45
union_find.find                          small        bend 1.81 1.91 1.84 1.61 1.62 2.64
                                                      ref  1.67 1.59 1.57 1.45 1.57 1.49
union_find.find                          medium       bend 1.65 1.37 1.65 1.72 1.73 2.29
                                                      ref  1.00 1.40 1.65 1.59 1.40 1.35
union_find.find                          large        bend 1.64 1.76 1.55 1.85 1.88 1.79
                                                      ref  1.63 1.59 1.55 1.47 1.54 1.50
union_find.union                         small        bend 7.32 4.64 4.77 8.05 7.45 5.03
                                                      ref  1.96 1.77 2.25 2.37 2.21 1.93
union_find.union                         medium       bend 6.42 11.83 2.17 4.73 4.56 3.50
                                                      ref  1.68 1.62 1.67 1.79 1.64 1.55
union_find.connected                     small        bend 2.48 13.75 4.71 2.83 2.79 2.75
                                                      ref  1.79 3.23 2.74 1.97 1.93 2.55
union_find.connected                     medium       bend 2.37 2.30 2.49 2.51 3.42 2.20
                                                      ref  2.18 1.59 1.60 2.57 1.78 1.84
union_find.connected                     large        bend 3.18 2.81 2.90 2.47 2.53 2.53
                                                      ref  2.17 1.97 1.98 2.03 1.89 1.91
union_find.component_size                small        bend 2.14 2.01 1.61 1.82 2.24 2.48
                                                      ref  1.59 1.75 1.77 2.10 1.68 1.90
union_find.component_size                medium       bend 1.40 5.06 1.95 1.76 1.70 1.55
                                                      ref  1.87 3.52 3.03 0.98 1.35 1.41
union_find.component_size                large        bend 1.64 1.53 1.62 1.58 1.61 1.55
                                                      ref  1.29 1.31 1.29 1.30 1.32 1.28
union_find.component_count               small        bend 1.00 1.01 1.02 1.00 1.01 1.00
                                                      ref  2.86 2.90 2.89 2.89 2.87 2.84
union_find.component_count               medium       bend 1.01 1.00 0.97 1.00 1.02 1.03
                                                      ref  2.98 2.88 2.88 2.86 2.89 2.86
union_find.component_count               large        bend 1.12 1.02 1.06 1.02 1.03 1.04
                                                      ref  2.96 2.88 2.97 2.89 2.87 2.93
union_find.new                           small        bend 35.67 34.67 32.67 35.00 27.00 34.33
                                                      ref  1.89 1.82 1.95 1.82 2.09 2.02
union_find.new                           medium       bend 33.82 34.12 33.82 34.12 34.71 34.71
                                                      ref  1.90 2.05 1.59 2.10 1.80 1.84
union_find.new                           large        bend 34.38 34.38 34.38 35.94 35.31 35.31
                                                      ref  1.73 1.83 1.63 1.82 1.92 1.92
union_find.new                           edge-empty   bend 34.81 36.35 36.92 34.81 35.58 38.08
                                                      ref  1.92 1.94 1.66 1.83 1.94 1.96
union_find.find                          edge-empty   bend 1.12 1.13 1.15 1.13 1.15 1.13
                                                      ref  1.34 1.03 1.01 1.06 1.02 1.01
union_find.union                         edge-empty   bend 3.44 3.41 3.38 3.41 3.41 3.47
                                                      ref  1.13 1.12 1.13 1.13 1.13 1.14
union_find.connected                     edge-empty   bend 1.61 1.56 1.56 1.58 1.59 1.59
                                                      ref  1.13 1.12 1.10 1.11 1.14 1.11
union_find.component_size                edge-empty   bend 1.22 1.36 1.13 1.15 1.16 1.12
                                                      ref  1.01 1.01 1.02 1.02 1.03 1.01
union_find.component_count               edge-empty   bend 1.03 1.02 1.02 1.00 0.99 1.02
                                                      ref  2.91 2.87 2.88 2.87 2.87 2.91
fenwick_tree.add                         small        bend 22.03 21.72 22.19 21.41 22.19 22.03
                                                      ref  22.52 19.65 19.70 19.23 19.50 19.47
fenwick_tree.add                         medium       bend 41.57 39.61 40.39 40.78 40.78 40.78
                                                      ref  36.87 36.78 37.28 36.87 36.61 37.01
fenwick_tree.add                         large        bend 58.33 66.67 55.88 54.90 56.37 59.31
                                                      ref  51.24 51.44 51.92 51.67 51.34 51.26
fenwick_tree.prefix_sum                  small        bend 22.35 21.91 22.21 22.35 22.65 22.94
                                                      ref  19.23 19.31 18.93 19.01 19.25 19.11
fenwick_tree.prefix_sum                  medium       bend 42.19 34.69 41.56 41.56 40.62 41.56
                                                      ref  37.18 37.00 37.37 37.39 37.25 37.34
fenwick_tree.prefix_sum                  large        bend 57.84 58.33 58.82 57.35 59.31 57.84
                                                      ref  52.74 52.60 52.33 52.56 51.33 52.59
fenwick_tree.range_sum                   small        bend 23.38 23.82 23.09 22.94 23.38 23.68
                                                      ref  23.16 19.97 19.97 19.87 19.79 19.80
fenwick_tree.range_sum                   medium       bend 42.19 41.56 41.88 41.88 46.56 43.12
                                                      ref  36.46 37.52 37.54 41.04 38.67 38.07
fenwick_tree.range_sum                   large        bend 14.69 16.33 16.72 16.33 14.38 17.58
                                                      ref  12.23 14.53 14.27 14.29 16.91 13.79
fenwick_tree.length                      small        bend 1.12 1.03 1.06 1.05 1.05 1.23
                                                      ref  3.02 3.07 3.07 3.07 2.88 3.11
fenwick_tree.length                      medium       bend 1.07 1.08 1.12 1.08 1.11 1.09
                                                      ref  3.05 3.13 3.05 3.13 3.10 3.16
fenwick_tree.length                      large        bend 1.12 1.11 1.10 1.10 1.10 1.09
                                                      ref  2.98 3.16 3.10 3.11 3.14 3.16
fenwick_tree.from_list                   small        bend 133.33 145.33 136.00 181.33 165.33 149.33
                                                      ref  25.59 25.69 34.19 31.12 31.03 29.81
fenwick_tree.from_list                   medium       bend 190.67 136.00 153.33 153.33 144.00 146.67
                                                      ref  26.69 27.13 29.06 29.61 27.81 26.56
fenwick_tree.from_list                   large        bend 141.18 149.26 145.59 148.53 145.59 161.76
                                                      ref  28.46 26.23 26.38 27.29 25.47 27.39
fenwick_tree.new                         small        bend 9.53 11.02 8.28 8.28 10.47 8.05
                                                      ref  10.52 12.02 14.18 12.25 13.33 12.70
fenwick_tree.new                         medium       bend 7.19 7.89 7.73 8.05 7.73 7.89
                                                      ref  13.47 14.14 12.86 13.00 13.81 15.66
fenwick_tree.new                         large        bend 7.69 8.38 8.19 8.62 8.31 8.38
                                                      ref  13.80 12.20 13.03 10.14 13.32 12.07
fenwick_tree.new                         edge-empty   bend 7.76 8.33 8.33 8.28 8.07 8.12
                                                      ref  14.59 12.81 12.59 13.62 13.30 14.83
fenwick_tree.from_list                   edge-empty   bend 181.43 161.43 162.86 164.29 191.43 187.14
                                                      ref  34.42 29.74 37.61 32.50 33.81 30.55
fenwick_tree.length                      edge-empty   bend 1.24 1.16 1.21 1.29 1.21 1.99
                                                      ref  3.53 3.57 3.41 3.41 3.61 4.74
fenwick_tree.add                         edge-empty   bend 2.76 2.37 2.06 2.55 2.14 3.78
                                                      ref  1.58 1.38 1.48 1.52 1.46 1.49
fenwick_tree.prefix_sum                  edge-empty   bend 3.17 2.41 3.15 4.13 3.33 2.81
                                                      ref  1.61 1.70 2.06 1.79 1.78 1.60
fenwick_tree.range_sum                   edge-empty   bend 4.77 4.38 4.22 4.22 4.30 4.30
                                                      ref  1.99 1.97 2.08 1.94 1.68 1.57
segment_tree.range_add                   small        bend 57.65 61.18 58.24 57.06 59.41 55.29
                                                      ref  36.20 37.03 36.49 28.92 37.10 37.15
segment_tree.range_add                   medium       bend 155.88 139.71 148.53 129.41 128.68 125.00
                                                      ref  68.41 90.46 85.26 70.42 91.55 68.83
segment_tree.range_add                   large        bend 49.26 57.35 51.47 53.68 64.34 59.56
                                                      ref  37.36 35.03 34.81 31.79 36.77 35.34
segment_tree.get                         small        bend 30.59 28.43 31.96 20.98 35.69 38.43
                                                      ref  3.34 4.17 4.07 4.02 4.63 4.93
segment_tree.get                         large        bend 73.47 80.97 78.89 68.51 76.70 92.16
                                                      ref  13.73 14.18 14.18 14.23 12.58 20.79
segment_tree.range_query                 small        bend 50.77 53.08 46.15 56.15 58.46 56.15
                                                      ref  29.32 32.26 27.62 35.20 36.89 36.02
segment_tree.range_query                 medium       bend 74.26 86.40 82.72 76.47 82.72 80.15
                                                      ref  49.57 55.01 58.40 51.32 55.35 56.65
segment_tree.range_query                 large        bend 37.30 24.61 26.56 24.80 22.85 25.78
                                                      ref  42.67 17.70 17.81 17.13 15.82 15.33
segment_tree.length                      small        bend 1.10 1.06 1.13 1.12 1.16 1.12
                                                      ref  2.78 2.72 2.72 2.96 2.92 2.88
segment_tree.length                      medium       bend 1.09 1.11 1.17 1.20 1.16 1.11
                                                      ref  2.74 2.83 2.80 2.72 2.91 2.76
segment_tree.length                      large        bend 1.12 1.15 1.08 1.17 1.60 1.12
                                                      ref  2.93 2.74 3.13 2.94 3.11 2.69
segment_tree.set                         small        bend 54.12 50.88 52.35 55.29 53.53 54.41
                                                      ref  12.64 13.21 13.19 13.16 13.22 13.63
segment_tree.set                         medium       bend 127.21 132.35 122.79 123.53 131.62 127.21
                                                      ref  29.96 28.60 27.10 26.56 24.71 28.45
segment_tree.set                         large        bend 234.92 209.52 173.02 184.13 198.41 203.17
                                                      ref  162.55 108.33 166.59 124.37 131.57 124.66
segment_tree.from_list                   small        bend 254.00 246.00 282.00 290.00 458.00 304.00
                                                      ref  69.56 187.64 63.89 50.12 103.92 93.26
segment_tree.from_list                   medium       bend 276.67 273.33 298.33 265.00 260.00 338.33
                                                      ref  78.28 73.37 69.22 75.81 73.73 79.78
segment_tree.from_list                   large        bend 232.69 311.54 182.69 621.15 325.00 257.69
                                                      ref  108.02 68.26 84.45 83.79 144.45 84.53
segment_tree.new                         small        bend 12.84 12.45 16.08 14.51 12.25 12.45
                                                      ref  13.34 13.77 15.57 12.98 12.93 11.30
segment_tree.new                         medium       bend 12.16 12.75 12.16 13.24 19.31 11.96
                                                      ref  12.80 14.59 17.83 14.72 13.10 8.31
segment_tree.new                         large        bend 26.88 13.59 10.78 12.81 12.50 13.59
                                                      ref  15.64 12.19 13.07 12.99 13.24 11.21
segment_tree.new                         edge-empty   bend 18.59 11.56 17.34 12.58 12.58 12.42
                                                      ref  16.09 18.67 14.27 13.41 13.47 12.99
segment_tree.from_list                   edge-empty   bend 310.00 285.00 395.00 307.50 287.50 287.50
                                                      ref  75.83 75.43 87.54 80.47 79.91 87.71
segment_tree.length                      edge-empty   bend 1.28 1.32 1.48 1.36 1.34 1.24
                                                      ref  3.65 4.24 3.37 3.46 3.38 3.03
segment_tree.get                         edge-empty   bend 1.48 1.55 1.68 1.36 1.49 1.46
                                                      ref  1.47 1.46 1.44 1.42 1.34 1.37
segment_tree.set                         edge-empty   bend 4.53 5.31 5.18 5.13 4.95 4.38
                                                      ref  2.08 1.46 1.49 1.46 1.43 1.42
segment_tree.range_query                 edge-empty   bend 10.31 10.62 10.16 10.62 9.61 10.23
                                                      ref  2.10 2.35 2.41 2.30 2.31 2.17
segment_tree.range_add                   edge-empty   bend 7.58 8.17 7.84 7.91 8.10 10.85
                                                      ref  3.33 3.65 3.41 2.80 4.07 2.71
prefix_trie.insert                       small        bend 986.67 1340.00 986.67 1706.67 680.00 1160.00
                                                      ref  198.81 159.01 221.80 181.88 205.29 226.53
prefix_trie.insert                       medium       bend 758.33 1175.00 600.00 883.33 1141.67 958.33
                                                      ref  138.06 148.70 167.71 142.97 152.40 136.60
prefix_trie.insert                       large        bend 849.41 671.39 869.75 991.82 2217.61 1251.22
                                                      ref  167.72 190.65 240.68 253.49 241.06 179.18
prefix_trie.lookup                       small        bend 278.00 448.00 314.00 302.00 298.00 396.00
                                                      ref  32.31 32.35 31.42 28.48 31.15 39.45
prefix_trie.lookup                       medium       bend 432.50 387.50 347.50 487.50 565.00 427.50
                                                      ref  64.02 58.59 84.19 75.12 73.84 60.80
prefix_trie.lookup                       large        bend 1035.94 667.19 521.88 1020.31 1435.94 626.56
                                                      ref  118.62 111.93 190.69 118.19 126.23 98.64
prefix_trie.remove                       small        bend 825.00 480.00 700.00 850.00 670.00 740.00
                                                      ref  84.55 95.72 95.89 110.27 97.39 96.41
prefix_trie.remove                       medium       bend 1110.00 1020.00 970.00 950.00 1000.00 990.00
                                                      ref  148.26 137.40 135.54 115.63 142.60 127.82
prefix_trie.remove                       large        bend 1726.56 1376.56 1381.25 1432.81 1489.06 1468.75
                                                      ref  245.13 205.35 219.29 247.69 227.59 188.55
prefix_trie.contains                     small        bend 373.33 333.33 355.00 305.00 315.00 341.67
                                                      ref  42.34 38.18 34.16 35.95 34.66 34.19
prefix_trie.contains                     medium       bend 419.23 530.77 473.08 488.46 476.92 546.15
                                                      ref  69.88 70.87 63.44 65.22 63.22 69.87
prefix_trie.contains                     large        bend 813.73 754.90 682.35 858.82 545.10 803.92
                                                      ref  163.79 124.27 112.03 124.76 132.20 127.17
prefix_trie.prefix_entries               small        bend 1588.24 1647.06 1552.94 1729.41 1764.71 1764.71
                                                      ref  97.58 106.40 120.24 115.99 109.21 114.05
prefix_trie.prefix_entries               medium       bend 55500.00 59500.00 55000.00 51000.00 53500.00 58000.00
                                                      ref  3003.50 3011.50 3091.00 2908.00 3083.00 2987.00
prefix_trie.prefix_entries               large        bend 841666.67 1791666.67 1691666.67 1891666.67 1225000.00 1733333.33
                                                      ref  46525.00 48708.33 49350.00 38791.67 54408.33 34366.67
prefix_trie.longest_prefix               small        bend 302.50 277.50 282.50 302.50 300.00 287.50
                                                      ref  37.59 33.89 41.32 34.52 37.07 40.55
prefix_trie.longest_prefix               medium       bend 345.83 387.50 408.33 341.67 370.83 414.58
                                                      ref  73.29 78.94 77.35 73.67 70.36 69.30
prefix_trie.longest_prefix               large        bend 853.12 643.75 609.38 751.56 575.00 575.00
                                                      ref  199.29 134.03 148.39 151.74 165.02 128.35
prefix_trie.new                          small        bend 1.39 1.38 1.38 1.29 1.41 1.37
                                                      ref  3.58 3.53 3.68 3.71 3.53 3.78
prefix_trie.new                          medium       bend 1.43 1.29 1.39 1.56 1.46 1.47
                                                      ref  3.51 3.56 3.76 3.55 3.90 3.43
prefix_trie.new                          large        bend 1.33 1.42 1.41 1.61 1.28 1.47
                                                      ref  3.99 3.75 3.80 3.57 3.88 3.79
prefix_trie.new                          edge-empty   bend 1.49 1.25 1.45 1.55 1.49 1.42
                                                      ref  3.45 3.70 3.44 3.56 3.31 3.59
prefix_trie.insert                       edge-empty   bend 1778.44 2255.78 1752.19 1413.59 1942.66 2079.69
                                                      ref  392.81 380.72 443.06 343.57 240.80 441.88
prefix_trie.lookup                       edge-empty   bend 228.00 194.00 200.00 176.00 174.00 176.00
                                                      ref  1.74 1.41 1.61 1.78 1.62 1.61
prefix_trie.remove                       edge-empty   bend 176.67 175.00 173.33 188.33 178.33 190.00
                                                      ref  2.33 2.32 2.51 2.31 2.31 2.54
prefix_trie.contains                     edge-empty   bend 238.33 235.00 230.00 195.00 190.00 170.00
                                                      ref  3.69 2.21 1.81 1.71 1.61 1.64
prefix_trie.prefix_entries               edge-empty   bend 23.82 26.76 23.53 27.79 25.74 28.09
                                                      ref  5.30 4.82 5.53 4.81 4.82 4.81
prefix_trie.longest_prefix               edge-empty   bend 176.67 188.33 180.00 185.00 175.00 183.33
                                                      ref  4.07 3.33 3.42 3.72 3.34 3.14
graph.add_vertex                         small        bend 158.67 182.67 180.00 172.00 168.00 166.67
                                                      ref  25.40 22.89 30.20 21.39 22.65 21.38
graph.add_vertex                         medium       bend 260.00 291.67 293.33 296.67 278.33 273.33
                                                      ref  40.48 35.98 40.84 38.53 38.55 34.34
graph.remove_vertex                      medium       bend 1719.30 247.68 2735.81 2230.13 5355.01 305.47
                                                      ref  140.41 174.05 144.50 794.16 235.23 257.11
graph.remove_vertex                      large        bend 290000.00 270000.00 280000.00 280000.00 270000.00 290000.00
                                                      ref  29812.50 30057.50 31287.50 27480.00 31772.50 32752.50
graph.add_edge                           small        bend 2040.00 1940.00 1960.00 1900.00 1880.00 1960.00
                                                      ref  90.82 77.98 97.42 72.60 90.52 79.14
graph.add_edge                           medium       bend 4000.00 5600.00 4925.00 4650.00 4600.00 4300.00
                                                      ref  438.18 489.75 549.42 417.52 403.30 366.52
graph.add_edge                           large        bend 3700.00 3833.33 3666.67 4000.00 3533.33 4166.67
                                                      ref  420.60 418.77 444.17 369.43 439.03 397.17
graph.remove_edge                        small        bend 300.00 291.43 260.00 260.00 257.14 280.00
                                                      ref  36.71 35.60 39.90 35.93 35.28 34.38
graph.remove_edge                        medium       bend 665.00 565.00 580.00 620.00 575.00 580.00
                                                      ref  83.59 80.14 82.28 81.14 88.31 86.78
graph.remove_edge                        large        bend 791.67 916.67 783.33 900.00 750.00 908.33
                                                      ref  145.76 111.78 125.03 128.20 123.86 111.33
graph.has_vertex                         small        bend 138.00 137.33 142.00 142.67 138.00 145.33
                                                      ref  21.02 18.95 20.01 19.91 20.33 18.15
graph.has_vertex                         medium       bend 230.77 250.00 248.08 230.77 234.62 250.00
                                                      ref  38.81 37.69 39.06 34.62 36.95 35.67
graph.has_vertex                         large        bend 329.41 398.04 400.00 386.27 400.00 494.12
                                                      ref  53.36 49.78 52.80 40.54 47.24 55.96
graph.has_edge                           small        bend 320.00 316.67 311.67 336.67 331.67 330.00
                                                      ref  43.63 35.88 42.70 38.62 44.94 41.64
graph.has_edge                           medium       bend 556.25 603.12 556.25 590.62 550.00 559.38
                                                      ref  79.05 71.18 84.63 73.22 79.06 71.66
graph.has_edge                           large        bend 840.00 860.00 826.67 800.00 853.33 753.33
                                                      ref  134.31 122.63 136.00 125.03 120.51 113.86
graph.neighbors                          small        bend 183.64 190.91 191.82 186.36 180.91 181.82
                                                      ref  24.34 23.09 22.31 23.22 23.55 21.88
graph.neighbors                          medium       bend 313.46 305.77 298.08 319.23 300.00 332.69
                                                      ref  41.57 36.29 40.17 36.12 41.73 39.30
graph.neighbors                          large        bend 650.98 470.59 435.29 458.82 484.31 484.31
                                                      ref  70.19 66.97 73.13 63.68 65.06 62.30
graph.vertices                           small        bend 938.46 961.54 1007.69 961.54 900.00 953.85
                                                      ref  44.06 35.77 36.82 33.36 41.40 40.38
graph.vertices                           medium       bend 15600.00 16133.33 15466.67 21466.67 23333.33 15600.00
                                                      ref  661.60 702.27 625.87 845.33 688.27 630.80
graph.vertices                           large        bend 132941.18 171764.71 147058.82 162352.94 152941.18 143529.41
                                                      ref  5483.53 5821.18 5478.82 5112.94 5136.47 4977.65
graph.edges                              small        bend 2825.00 2825.00 3000.00 2950.00 2925.00 2975.00
                                                      ref  152.95 146.68 160.60 159.88 161.75 164.03
graph.edges                              medium       bend 62000.00 58000.00 57000.00 57000.00 59500.00 57000.00
                                                      ref  2754.50 2752.00 2945.00 2931.00 2746.00 2915.50
graph.edges                              large        bend 616666.67 650000.00 530000.00 586666.67 683333.33 593333.33
                                                      ref  25110.00 24440.00 29290.00 24796.67 26703.33 24670.00
graph.new                                small        bend 4.71 5.64 5.00 5.10 5.05 5.98
                                                      ref  2.37 2.12 2.18 2.01 2.13 2.07
graph.new                                medium       bend 4.61 5.70 4.30 6.45 5.12 4.77
                                                      ref  2.19 2.08 2.23 2.12 2.49 2.17
graph.new                                large        bend 5.49 7.21 6.72 5.65 4.56 4.97
                                                      ref  2.18 2.82 2.31 1.98 2.22 2.02
graph.new                                edge-empty   bend 5.35 4.92 4.45 5.23 5.35 5.27
                                                      ref  2.26 2.07 2.21 2.07 2.19 2.03
graph.add_vertex                         edge-empty   bend 22.65 35.88 30.44 30.00 31.91 29.12
                                                      ref  1.68 1.46 1.42 1.51 1.35 1.35
graph.remove_vertex                      edge-empty   bend 7.89 9.14 8.12 9.22 8.67 10.31
                                                      ref  1.30 1.25 1.36 1.48 1.41 1.37
graph.add_edge                           edge-empty   bend 18.92 15.59 16.27 15.69 13.92 16.27
                                                      ref  1.43 1.40 1.49 1.21 1.47 1.26
graph.has_vertex                         edge-empty   bend 6.82 7.14 6.93 6.82 7.34 7.08
                                                      ref  1.41 1.29 1.41 1.26 1.36 1.30
graph.has_edge                           edge-empty   bend 16.08 17.35 22.35 21.47 27.75 16.18
                                                      ref  1.40 2.12 1.81 1.80 1.71 1.31
graph.neighbors                          edge-empty   bend 8.36 8.59 8.67 9.06 8.52 9.38
                                                      ref  1.30 1.30 1.30 1.29 1.30 1.48
graph.vertices                           edge-empty   bend 6.09 5.16 5.16 5.00 4.84 5.26
                                                      ref  5.50 3.97 3.95 3.80 4.05 3.34
graph.edges                              edge-empty   bend 5.47 6.17 3.95 6.09 5.51 7.03
                                                      ref  4.35 4.30 6.46 4.53 4.89 5.22
```

## Failed measurements

A row is FAILED when the difference `A - B` cannot be driven above the
clock minima on both sides, *including* when it comes out negative.
Regions A and B now differ only in the trip count (`2k` against `k`)
and the region order is alternated over the samples, so neither the
deallocation asymmetry of the earlier two-region form nor a monotone
machine drift can produce a failure here; what remains is an operation
whose per-iteration cost is too small, or a round whose build is too
expensive, to drive the difference above the clock minima within the
per-row budget. Such rows are reported as failures, never as numbers.

```
doubly_linked_list.push_back / large: sample 4: A-B = 45000000ns (bend) / 3350000ns (reference), below the 50000000ns / 100000ns minima
doubly_linked_list.remove / small: sample 0: A-B = 15000000ns (bend) / 5536000ns (reference), below the 50000000ns / 100000ns minima
bitset.difference / small: sample 0: A-B = 110000000ns (bend) / -16284000ns (reference), below the 50000000ns / 100000ns minima
bitset.xor / medium: sample 1: A-B = 49000000ns (bend) / 89528000ns (reference), below the 50000000ns / 100000ns minima
union_find.union / large: sample 0: A-B = -293000000ns (bend) / 8032000ns (reference), below the 50000000ns / 100000ns minima
segment_tree.get / medium: sample 0: A-B = 185000000ns (bend) / -1881000ns (reference), below the 50000000ns / 100000ns minima
graph.add_vertex / large: sample 3: A-B = -108000000ns (bend) / 14621000ns (reference), below the 50000000ns / 100000ns minima
graph.remove_vertex / small: sample 4: A-B = -44000000ns (bend) / 21446000ns (reference), below the 50000000ns / 100000ns minima
graph.remove_edge / edge-empty: sample 4: A-B = 255000000ns (bend) / -9964000ns (reference), below the 50000000ns / 100000ns minima
```

Raw per-sample log: `build/bench/logs/samples.log`;
machine-readable evidence with source and artifact hashes:
`build/performance/report.json`.
