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
| measured, within 2.5x | 245 |
| measured, **over 2.5x** | 160 |
| of those, unflagged (varying argument, reference > 3 ns/op) | 64 |
| FAILED measurement (not resolvable above the clock minima) | 3 |
| total rows in `benchmarks/workloads.py` | 408 |

**The 2.5x contract is NOT met.** 160 measured workloads exceed it
(worst unflagged row: `prefix_trie.longest_prefix` / edge-empty at **50.90x**;
worst row of any kind: `prefix_trie.lookup` / edge-empty at **110.14x**)
and 3 workloads could not be measured at all. The nine `lru.*`
operations the contract requires have **no rows in this frozen table**:
the table lives in the protected `benchmarks/workloads.py`. The
benchmarked cache is `src/lru/fast.bend` (native, proven:
`proofs/lru_fast.bend`), with its optimized C reference
`benchmarks/native/lru.c`; its rows are proposed in
`docs/BENCHMARK_CHANGE_PROPOSAL.md` and measured with this runner's own
machinery by `python3 tools/lru_measure.py` (supplemental report
`build/performance/lru_experiment.json`, table in
`docs/C_EQUIVALENCE.md`). The keyed `lru.*` rows are far over 2.5x there
as well; the native crit-bit `Map` bounds them. (The retained cache
itself cannot be compiled natively: `docs/VALIDATION.md`, "arity over 255".)

## All rows

`bend` and `ref` are nanoseconds per operation (median of the samples).

### `balanced_search_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 300000 | 435.00 | 29.99 | 14.50x **over** | yes | - |
| `insert` | medium | 4096 | 100000 | 1160.00 | 85.22 | 13.61x **over** | yes | - |
| `insert` | large | 131072 | 120000 | 1829.17 | 187.16 | 9.77x **over** | yes | - |
| `remove` | small | 64 | 200000 | 920.00 | 70.90 | 12.98x **over** | yes | restoring pair |
| `remove` | medium | 4096 | 50000 | 2120.00 | 166.18 | 12.76x **over** | yes | restoring pair |
| `remove` | large | 131072 | 60000 | 2891.67 | 268.85 | 10.76x **over** | yes | restoring pair |
| `lookup` | small | 64 | 800000 | 140.62 | 20.86 | 6.74x **over** | yes | - |
| `lookup` | medium | 4096 | 300000 | 330.00 | 52.11 | 6.33x **over** | yes | - |
| `lookup` | large | 131072 | 480000 | 503.12 | 113.54 | 4.43x **over** | yes | - |
| `contains` | small | 64 | 700000 | 150.71 | 25.52 | 5.90x **over** | yes | - |
| `contains` | medium | 4096 | 600000 | 326.67 | 48.83 | 6.69x **over** | yes | - |
| `contains` | large | 131072 | 1020000 | 530.39 | 107.16 | 4.95x **over** | yes | - |
| `min` | small | 64 | 2600000 | 45.38 | 1.32 | 34.51x **over** | yes | argument-free, barrier-dominated |
| `min` | medium | 4096 | 700000 | 139.29 | 5.19 | 26.84x **over** | yes | argument-free |
| `min` | large | 131072 | 1100000 | 174.55 | 6.22 | 28.07x **over** | yes | argument-free |
| `max` | small | 64 | 2200000 | 50.68 | 1.31 | 38.61x **over** | yes | argument-free, barrier-dominated |
| `max` | medium | 4096 | 1600000 | 142.81 | 4.31 | 33.16x **over** | yes | argument-free |
| `max` | large | 131072 | 3200000 | 168.91 | 5.80 | 29.12x **over** | yes | argument-free |
| `lower_bound` | small | 64 | 800000 | 151.88 | 21.34 | 7.12x **over** | yes | - |
| `lower_bound` | medium | 4096 | 300000 | 358.33 | 52.44 | 6.83x **over** | yes | - |
| `lower_bound` | large | 131072 | 340000 | 519.12 | 105.89 | 4.90x **over** | yes | - |
| `range` | small | 64 | 384000 | 256.51 | 38.13 | 6.73x **over** | yes | - |
| `range` | medium | 4096 | 7800 | 13525.64 | 1067.63 | 12.67x **over** | yes | - |
| `range` | large | 131072 | 1280 | 116015.62 | 10255.08 | 11.31x **over** | yes | - |
| `to_list` | small | 64 | 256000 | 736.33 | 55.41 | 13.29x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 1500 | 70333.33 | 4455.33 | 15.79x **over** | yes | argument-free |
| `to_list` | large | 131072 | 255 | 2437254.90 | 248945.10 | 9.79x **over** | yes | argument-free |
| `length` | small | 64 | 89600000 | 1.08 | 3.09 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 108800000 | 1.12 | 3.17 | 0.35x | yes | argument-free |
| `length` | large | 131072 | 204800000 | 1.10 | 3.13 | 0.35x | yes | argument-free |
| `new` | small | 64 | 89600000 | 1.16 | 2.89 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 102400000 | 1.09 | 2.74 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | large | 131072 | 172800000 | 1.12 | 2.89 | 0.39x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 83200000 | 1.14 | 2.78 | 0.41x | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 96000000 | 1.10 | 3.11 | 0.35x | yes | argument-free |
| `insert` | edge-empty | 0 | 3400000 | 46.47 | 3.52 | 13.21x **over** | yes | - |
| `remove` | edge-empty | 0 | 19200000 | 7.06 | 3.18 | 2.22x | yes | - |
| `lookup` | edge-empty | 0 | 25600000 | 4.63 | 1.40 | 3.30x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 25600000 | 4.63 | 1.36 | 3.41x **over** | yes | barrier-dominated |
| `min` | edge-empty | 0 | 25600000 | 4.22 | 1.22 | 3.45x **over** | yes | argument-free, barrier-dominated |
| `max` | edge-empty | 0 | 25600000 | 4.51 | 1.41 | 3.20x **over** | yes | argument-free, barrier-dominated |
| `lower_bound` | edge-empty | 0 | 15300000 | 7.03 | 1.41 | 4.97x **over** | yes | barrier-dominated |
| `range` | edge-empty | 0 | 20400000 | 5.32 | 5.31 | 1.00x | yes | - |
| `to_list` | edge-empty | 0 | 25600000 | 5.12 | 4.21 | 1.22x | yes | argument-free |

### `binary_heap`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 12800000 | 14.26 | 9.18 | 1.55x | yes | - |
| `push` | medium | 4096 | 9600000 | 14.27 | 9.19 | 1.55x | yes | - |
| `push` | large | 131072 | 8912896 | 15.15 | 9.18 | 1.65x | yes | - |
| `peek` | small | 64 | 102400000 | 0.99 | 1.00 | 0.99x | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 108800000 | 1.00 | 1.00 | 1.00x | yes | argument-free, barrier-dominated |
| `peek` | large | 131072 | 163200000 | 1.00 | 1.00 | 1.00x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 102400000 | 1.00 | 2.85 | 0.35x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 108800000 | 1.25 | 3.22 | 0.39x | yes | argument-free |
| `length` | large | 131072 | 108800000 | 1.46 | 3.91 | 0.37x | yes | argument-free |
| `from_list` | small | 64 | 850000 | 165.29 | 81.50 | 2.03x | yes | - |
| `from_list` | medium | 4096 | 650000 | 190.77 | 83.00 | 2.30x | yes | - |
| `from_list` | large | 131072 | 680000 | 182.35 | 86.52 | 2.11x | yes | - |
| `to_sorted_list` | small | 64 | 68000 | 1860.29 | 840.34 | 2.21x | yes | argument-free |
| `to_sorted_list` | medium | 4096 | 600 | 187500.00 | 76250.00 | 2.46x | yes | argument-free |
| `to_sorted_list` | large | 131072 | 15 | 9766666.67 | 5002700.00 | 1.95x | yes | argument-free |
| `pop` | small | 64 | 3400000 | 47.35 | 20.01 | 2.37x | yes | restoring pair |
| `pop` | medium | 4096 | 1300000 | 90.00 | 39.16 | 2.30x | yes | restoring pair |
| `pop` | large | 131072 | 1040000 | 133.65 | 51.98 | 2.57x **over** | yes | restoring pair |
| `new` | small | 64 | 76800000 | 3.42 | 3.06 | 1.12x | yes | argument-free |
| `new` | medium | 4096 | 40800000 | 2.93 | 3.22 | 0.91x | yes | argument-free |
| `new` | large | 131072 | 28800000 | 3.33 | 3.19 | 1.04x | yes | argument-free |
| `new` | edge-empty | 0 | 64000000 | 3.06 | 2.95 | 1.04x | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 166400000 | 1.11 | 3.10 | 0.36x | yes | argument-free |
| `push` | edge-empty | 0 | 10200000 | 17.60 | 11.14 | 1.58x | yes | - |
| `peek` | edge-empty | 0 | 108800000 | 1.14 | 1.14 | 1.00x | yes | argument-free, barrier-dominated |
| `pop` | edge-empty | 0 | 96000000 | 1.17 | 1.21 | 0.97x | yes | barrier-dominated |
| `from_list` | edge-empty | 0 | 900000 | 127.78 | 61.69 | 2.07x | yes | - |
| `to_sorted_list` | edge-empty | 0 | 12800000 | 11.64 | 5.46 | 2.13x | yes | argument-free |

### `bitset`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `set` | small | 64 | 64000000 | 1.91 | 1.79 | 1.07x | yes | barrier-dominated |
| `set` | medium | 4096 | 64000000 | 1.57 | 1.43 | 1.10x | yes | barrier-dominated |
| `set` | large | 262144 | 83200000 | 1.53 | 1.38 | 1.11x | yes | barrier-dominated |
| `clear` | small | 64 | 64000000 | 1.87 | 1.69 | 1.10x | yes | barrier-dominated |
| `clear` | medium | 4096 | 70400000 | 1.63 | 1.46 | 1.12x | yes | barrier-dominated |
| `clear` | large | 262144 | 108800000 | 1.53 | 1.41 | 1.09x | yes | barrier-dominated |
| `get` | small | 64 | 64000000 | 1.95 | 1.71 | 1.14x | yes | barrier-dominated |
| `get` | medium | 4096 | 57600000 | 1.83 | 1.44 | 1.27x | yes | barrier-dominated |
| `get` | large | 262144 | 108800000 | 1.76 | 1.47 | 1.20x | yes | barrier-dominated |
| `count` | small | 64 | 1700000 | 65.00 | 5.06 | 12.86x **over** | yes | argument-free |
| `count` | medium | 4096 | 40000 | 3725.00 | 244.45 | 15.24x **over** | yes | argument-free |
| `count` | large | 262144 | 500 | 238000.00 | 15393.00 | 15.46x **over** | yes | argument-free |
| `length` | small | 64 | 89600000 | 1.10 | 3.21 | 0.34x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.26 | 3.51 | 0.36x | yes | argument-free |
| `length` | large | 262144 | 83200000 | 1.16 | 3.42 | 0.34x | yes | argument-free |
| `to_list` | small | 64 | 340000 | 397.06 | 84.02 | 4.73x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 6000 | 20833.33 | 4927.92 | 4.23x **over** | yes | argument-free |
| `to_list` | large | 262144 | 100 | 1900000.00 | 330645.00 | 5.75x **over** | yes | argument-free |
| `union` | small | 64 | 19200000 | 6.90 | 1.54 | 4.48x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 2560000 | 67.77 | 63.11 | 1.07x | yes | - |
| `union` | large | 262144 | 32000 | 3687.50 | 3713.62 | 0.99x | yes | - |
| `intersection` | small | 64 | 16000000 | 6.38 | 1.53 | 4.18x **over** | yes | barrier-dominated |
| `intersection` | medium | 4096 | 2040000 | 67.16 | 61.90 | 1.08x | yes | - |
| `intersection` | large | 262144 | 32000 | 3812.50 | 4057.81 | 0.94x | yes | - |
| `difference` | small | 64 | 19200000 | 6.93 | 1.38 | 5.03x **over** | yes | barrier-dominated |
| `difference` | medium | 4096 | 2560000 | 79.69 | 69.40 | 1.15x | yes | - |
| `difference` | large | 262144 | 32000 | 3859.38 | 3966.44 | 0.97x | yes | - |
| `xor` | small | 64 | 16000000 | 6.88 | 1.43 | 4.80x **over** | yes | barrier-dominated |
| `xor` | medium | 4096 | 2560000 | 72.85 | 67.91 | 1.07x | yes | - |
| `xor` | large | 262144 | 51000 | 3725.49 | 4026.05 | 0.93x | yes | - |
| `new` | small | 64 | 38400000 | 3.49 | 12.68 | 0.28x | yes | argument-free |
| `new` | medium | 4096 | 30600000 | 3.53 | 12.38 | 0.29x | yes | argument-free |
| `new` | large | 262144 | 32000000 | 3.47 | 12.68 | 0.27x | yes | argument-free |
| `new` | edge-empty | 0 | 38400000 | 3.29 | 11.94 | 0.28x | yes | argument-free |
| `length` | edge-empty | 0 | 89600000 | 1.10 | 3.18 | 0.35x | yes | argument-free |
| `get` | edge-empty | 0 | 89600000 | 1.37 | 1.29 | 1.06x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 76800000 | 1.37 | 1.32 | 1.04x | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 76800000 | 1.37 | 1.31 | 1.05x | yes | barrier-dominated |
| `count` | edge-empty | 0 | 6000000 | 34.67 | 4.39 | 7.89x **over** | yes | argument-free |
| `union` | edge-empty | 0 | 25600000 | 5.47 | 1.30 | 4.21x **over** | yes | barrier-dominated |
| `intersection` | edge-empty | 0 | 25600000 | 5.23 | 1.30 | 4.03x **over** | yes | barrier-dominated |
| `difference` | edge-empty | 0 | 25600000 | 5.78 | 1.33 | 4.35x **over** | yes | barrier-dominated |
| `xor` | edge-empty | 0 | 25600000 | 5.41 | 1.30 | 4.18x **over** | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 2600000 | 40.19 | 4.36 | 9.21x **over** | yes | argument-free |

### `deque`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 25600000 | 6.74 | 1.54 | 4.38x **over** | yes | barrier-dominated |
| `push_front` | medium | 4096 | 15300000 | 6.96 | 1.56 | 4.46x **over** | yes | barrier-dominated |
| `push_front` | large | 262144 | 13369344 | 8.15 | 1.78 | 4.57x **over** | yes | barrier-dominated |
| `push_back` | small | 64 | 15600000 | 7.37 | 1.57 | 4.71x **over** | yes | barrier-dominated |
| `push_back` | medium | 4096 | 19200000 | 8.39 | 1.67 | 5.03x **over** | yes | barrier-dominated |
| `push_back` | large | 262144 | 13369344 | 8.49 | 1.63 | 5.21x **over** | yes | barrier-dominated |
| `peek_front` | small | 64 | 76800000 | 1.31 | 1.34 | 0.97x | yes | argument-free, barrier-dominated |
| `peek_front` | medium | 4096 | 153600000 | 1.27 | 1.33 | 0.96x | yes | argument-free, barrier-dominated |
| `peek_front` | large | 262144 | 108800000 | 1.26 | 1.30 | 0.97x | yes | argument-free, barrier-dominated |
| `peek_back` | small | 64 | 153600000 | 1.27 | 1.30 | 0.97x | yes | argument-free, barrier-dominated |
| `peek_back` | medium | 4096 | 96000000 | 1.27 | 1.42 | 0.90x | yes | argument-free, barrier-dominated |
| `peek_back` | large | 262144 | 83200000 | 1.26 | 1.30 | 0.96x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 153600000 | 1.20 | 3.39 | 0.36x | yes | argument-free |
| `length` | medium | 4096 | 153600000 | 1.19 | 3.46 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 86700000 | 1.23 | 3.50 | 0.35x | yes | argument-free |
| `to_list` | small | 64 | 160000 | 731.25 | 103.08 | 7.09x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 3000 | 35500.00 | 7095.00 | 5.00x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 2200000.00 | 456160.00 | 4.82x **over** | yes | argument-free |
| `pop_front` | small | 64 | 25600000 | 5.37 | 8.12 | 0.66x | yes | restoring pair |
| `pop_front` | medium | 4096 | 25600000 | 5.00 | 8.01 | 0.62x | yes | restoring pair |
| `pop_front` | large | 262144 | 22400000 | 5.71 | 8.22 | 0.69x | yes | restoring pair |
| `pop_back` | small | 64 | 25600000 | 5.45 | 8.49 | 0.64x | yes | restoring pair |
| `pop_back` | medium | 4096 | 25600000 | 4.92 | 8.02 | 0.61x | yes | restoring pair |
| `pop_back` | large | 262144 | 20400000 | 5.17 | 8.31 | 0.62x | yes | restoring pair |
| `new` | small | 64 | 38400000 | 3.91 | 1.48 | 2.64x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 30600000 | 3.82 | 1.52 | 2.52x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 262144 | 51000000 | 3.91 | 1.61 | 2.43x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 38400000 | 3.96 | 1.52 | 2.61x **over** | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 76800000 | 1.20 | 3.47 | 0.35x | yes | argument-free |
| `push_front` | edge-empty | 0 | 20400000 | 6.76 | 1.64 | 4.12x **over** | yes | barrier-dominated |
| `push_back` | edge-empty | 0 | 20400000 | 7.82 | 1.71 | 4.58x **over** | yes | barrier-dominated |
| `pop_front` | edge-empty | 0 | 76800000 | 1.27 | 1.27 | 1.00x | yes | barrier-dominated |
| `pop_back` | edge-empty | 0 | 89600000 | 1.24 | 1.30 | 0.96x | yes | barrier-dominated |
| `peek_front` | edge-empty | 0 | 89600000 | 1.27 | 1.32 | 0.96x | yes | argument-free, barrier-dominated |
| `peek_back` | edge-empty | 0 | 89600000 | 1.34 | 1.45 | 0.92x | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 20400000 | 7.40 | 1.51 | 4.89x **over** | yes | argument-free, barrier-dominated |

### `doubly_linked_list`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 10200000 | 10.69 | 4.46 | 2.40x | yes | - |
| `push_front` | medium | 2048 | 10200000 | 11.23 | 4.49 | 2.50x | yes | - |
| `push_front` | large | 32768 | 10485760 | 12.92 | 4.03 | 3.21x **over** | yes | - |
| `push_back` | small | 64 | 12800000 | 10.90 | 4.52 | 2.41x | yes | - |
| `push_back` | medium | 2048 | 9600000 | 10.83 | 4.30 | 2.52x **over** | yes | - |
| `push_back` | large | 32768 | 8388608 | 14.54 | 5.21 | 2.79x **over** | yes | - |
| `insert_before` | small | 64 | 10200000 | 13.09 | 5.18 | 2.53x **over** | yes | - |
| `insert_before` | medium | 2048 | 10200000 | 10.93 | 4.77 | 2.29x | yes | - |
| `insert_before` | large | 32768 | 12582912 | 18.20 | 5.89 | 3.09x **over** | yes | - |
| `insert_after` | small | 64 | 10200000 | 13.09 | 5.00 | 2.62x **over** | yes | - |
| `insert_after` | medium | 2048 | 9600000 | 13.91 | 6.13 | 2.27x | yes | - |
| `insert_after` | large | 32768 | 12582912 | 19.47 | 5.89 | 3.30x **over** | yes | - |
| `get` | small | 64 | 44800000 | 2.08 | 1.80 | 1.15x | yes | barrier-dominated |
| `get` | medium | 2048 | 41600000 | 2.09 | 1.77 | 1.18x | yes | barrier-dominated |
| `get` | large | 32768 | 87040000 | 2.23 | 1.71 | 1.30x | yes | barrier-dominated |
| `set` | small | 64 | 44800000 | 2.29 | 1.94 | 1.18x | yes | barrier-dominated |
| `set` | medium | 2048 | 48000000 | 2.02 | 1.68 | 1.20x | yes | barrier-dominated |
| `set` | large | 32768 | 81920000 | 2.01 | 1.77 | 1.14x | yes | barrier-dominated |
| `next` | small | 64 | 44800000 | 2.47 | 2.13 | 1.16x | yes | barrier-dominated |
| `next` | medium | 2048 | 54400000 | 2.46 | 1.93 | 1.27x | yes | barrier-dominated |
| `next` | large | 32768 | 66560000 | 2.57 | 2.04 | 1.26x | yes | barrier-dominated |
| `prev` | small | 64 | 38400000 | 2.75 | 2.29 | 1.20x | yes | barrier-dominated |
| `prev` | medium | 2048 | 54400000 | 2.45 | 1.90 | 1.29x | yes | barrier-dominated |
| `prev` | large | 32768 | 66560000 | 2.52 | 2.14 | 1.18x | yes | barrier-dominated |
| `length` | small | 64 | 70400000 | 1.31 | 3.73 | 0.35x | yes | argument-free |
| `length` | medium | 2048 | 134400000 | 1.41 | 4.11 | 0.34x | yes | argument-free |
| `length` | large | 32768 | 81920000 | 1.51 | 3.91 | 0.39x | yes | argument-free |
| `to_list` | small | 64 | 260000 | 575.00 | 110.45 | 5.21x **over** | yes | argument-free |
| `to_list` | medium | 2048 | 7800 | 15769.23 | 3792.44 | 4.16x **over** | yes | argument-free |
| `to_list` | large | 32768 | 420 | 352380.95 | 75730.95 | 4.65x **over** | yes | argument-free |
| `remove` | small | 64 | - | FAILED | FAILED | - | - | sample 1: A-B = 37000000ns (bend) / 113091000ns (reference), below the 50000000ns / 100000ns minima |
| `remove` | medium | 2048 | 16777216 | 7.51 | 6.67 | 1.13x | yes | - |
| `remove` | large | 32768 | 27262976 | 7.78 | 7.41 | 1.05x | yes | - |
| `new` | small | 64 | 12800000 | 8.12 | 2.64 | 3.07x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 2048 | 12800000 | 8.75 | 2.88 | 3.04x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 32768 | 12800000 | 8.40 | 2.77 | 3.03x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 19200000 | 8.26 | 2.64 | 3.13x **over** | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 108800000 | 1.00 | 2.85 | 0.35x | yes | argument-free, barrier-dominated |
| `push_front` | edge-empty | 0 | 15300000 | 7.39 | 3.07 | 2.40x | yes | - |
| `push_back` | edge-empty | 0 | 19200000 | 7.40 | 3.07 | 2.41x | yes | - |
| `insert_before` | edge-empty | 0 | 96000000 | 1.12 | 1.01 | 1.11x | yes | barrier-dominated |
| `insert_after` | edge-empty | 0 | 166400000 | 1.12 | 1.01 | 1.11x | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 96000000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `get` | edge-empty | 0 | 96000000 | 1.11 | 1.02 | 1.09x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 96000000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `next` | edge-empty | 0 | 166400000 | 1.12 | 1.02 | 1.10x | yes | barrier-dominated |
| `prev` | edge-empty | 0 | 96000000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 57600000 | 1.86 | 3.40 | 0.55x | yes | argument-free |

### `dynamic_array`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 25600000 | 7.25 | 4.29 | 1.69x | yes | - |
| `push` | medium | 4096 | 12800000 | 8.16 | 4.66 | 1.75x | yes | - |
| `push` | large | 262144 | 16777216 | 9.06 | 6.38 | 1.42x | yes | - |
| `get` | small | 64 | 51200000 | 2.09 | 1.73 | 1.20x | yes | barrier-dominated |
| `get` | medium | 4096 | 57600000 | 1.93 | 1.63 | 1.18x | yes | barrier-dominated |
| `get` | large | 262144 | 48000000 | 2.08 | 1.65 | 1.26x | yes | barrier-dominated |
| `set` | small | 64 | 64000000 | 1.82 | 1.74 | 1.05x | yes | barrier-dominated |
| `set` | medium | 4096 | 70400000 | 1.63 | 1.57 | 1.04x | yes | barrier-dominated |
| `set` | large | 262144 | 76800000 | 2.32 | 2.19 | 1.06x | yes | barrier-dominated |
| `length` | small | 64 | 64000000 | 1.66 | 4.96 | 0.33x | yes | argument-free |
| `length` | medium | 4096 | 115200000 | 1.56 | 4.05 | 0.39x | yes | argument-free |
| `length` | large | 262144 | 83200000 | 1.30 | 3.72 | 0.35x | yes | argument-free |
| `capacity` | small | 64 | 153600000 | 1.26 | 3.26 | 0.39x | yes | argument-free |
| `capacity` | medium | 4096 | 76800000 | 1.22 | 3.04 | 0.40x | yes | argument-free |
| `capacity` | large | 262144 | 108800000 | 1.22 | 3.04 | 0.40x | yes | argument-free |
| `reserve` | small | 64 | 25600000 | 4.98 | 1.56 | 3.18x **over** | yes | barrier-dominated |
| `reserve` | medium | 4096 | 25600000 | 4.84 | 1.53 | 3.17x **over** | yes | barrier-dominated |
| `reserve` | large | 262144 | 22400000 | 4.84 | 1.53 | 3.17x **over** | yes | barrier-dominated |
| `to_list` | small | 64 | 160000 | 675.00 | 103.56 | 6.52x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 3000 | 36000.00 | 6371.33 | 5.65x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 2390000.00 | 471450.00 | 5.07x **over** | yes | argument-free |
| `clear` | small | 64 | 2600000 | 71.73 | 8.66 | 8.28x **over** | yes | - |
| `clear` | medium | 4096 | 40000 | 3762.50 | 661.96 | 5.68x **over** | yes | - |
| `clear` | large | 262144 | 500 | 231000.00 | 14981.00 | 15.42x **over** | yes | - |
| `pop` | small | 64 | 20400000 | 6.18 | 4.03 | 1.53x | yes | restoring pair |
| `pop` | medium | 4096 | 38400000 | 5.78 | 3.95 | 1.46x | yes | restoring pair |
| `pop` | large | 262144 | 18700000 | 5.40 | 3.76 | 1.44x | yes | restoring pair |
| `new` | small | 64 | 25600000 | 4.77 | 3.22 | 1.48x | yes | argument-free |
| `new` | medium | 4096 | 25600000 | 4.75 | 3.28 | 1.45x | yes | argument-free |
| `new` | large | 262144 | 40800000 | 5.21 | 3.52 | 1.48x | yes | argument-free |
| `new` | edge-empty | 0 | 25600000 | 4.92 | 3.21 | 1.53x | yes | argument-free |
| `length` | edge-empty | 0 | 89600000 | 1.19 | 3.38 | 0.35x | yes | argument-free |
| `capacity` | edge-empty | 0 | 89600000 | 1.17 | 3.04 | 0.38x | yes | argument-free |
| `get` | edge-empty | 0 | 76800000 | 1.45 | 1.30 | 1.11x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 76800000 | 1.54 | 1.46 | 1.05x | yes | barrier-dominated |
| `push` | edge-empty | 0 | 20400000 | 7.48 | 4.20 | 1.78x | yes | - |
| `pop` | edge-empty | 0 | 76800000 | 1.26 | 1.31 | 0.96x | yes | barrier-dominated |
| `reserve` | edge-empty | 0 | 25600000 | 4.67 | 1.42 | 3.28x **over** | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 25600000 | 4.41 | 2.40 | 1.84x | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 25600000 | 5.45 | 2.39 | 2.28x | yes | argument-free, barrier-dominated |

### `fenwick_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add` | small | 64 | 6400000 | 25.31 | 22.49 | 1.13x | yes | - |
| `add` | medium | 4096 | 2600000 | 51.73 | 45.32 | 1.14x | yes | - |
| `add` | large | 262144 | 2040000 | 69.36 | 64.75 | 1.07x | yes | - |
| `prefix_sum` | small | 64 | 3400000 | 29.26 | 24.11 | 1.21x | yes | - |
| `prefix_sum` | medium | 4096 | 2550000 | 47.45 | 43.40 | 1.09x | yes | - |
| `prefix_sum` | large | 262144 | 1280000 | 73.83 | 66.54 | 1.11x | yes | - |
| `range_sum` | small | 64 | 5100000 | 27.65 | 23.33 | 1.18x | yes | - |
| `range_sum` | medium | 4096 | 3400000 | 50.74 | 44.06 | 1.15x | yes | - |
| `range_sum` | large | 262144 | 6400000 | 16.41 | 14.29 | 1.15x | yes | - |
| `length` | small | 64 | 179200000 | 1.11 | 3.16 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.09 | 3.20 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 108800000 | 1.10 | 3.18 | 0.35x | yes | argument-free |
| `from_list` | small | 64 | 1500000 | 155.00 | 28.39 | 5.46x **over** | yes | - |
| `from_list` | medium | 4096 | 1200000 | 157.92 | 30.10 | 5.25x **over** | yes | - |
| `from_list` | large | 262144 | 1040000 | 144.23 | 27.00 | 5.34x **over** | yes | - |
| `new` | small | 64 | 20400000 | 7.50 | 12.49 | 0.60x | yes | argument-free |
| `new` | medium | 4096 | 20400000 | 7.43 | 12.20 | 0.61x | yes | argument-free |
| `new` | large | 262144 | 16000000 | 7.22 | 12.18 | 0.59x | yes | argument-free |
| `new` | edge-empty | 0 | 12800000 | 7.58 | 12.74 | 0.59x | yes | argument-free |
| `from_list` | edge-empty | 0 | 700000 | 145.71 | 27.96 | 5.21x **over** | yes | - |
| `length` | edge-empty | 0 | 76800000 | 1.11 | 3.11 | 0.36x | yes | argument-free |
| `add` | edge-empty | 0 | 64000000 | 2.13 | 1.38 | 1.55x | yes | barrier-dominated |
| `prefix_sum` | edge-empty | 0 | 76800000 | 2.29 | 1.27 | 1.80x | yes | barrier-dominated |
| `range_sum` | edge-empty | 0 | 25600000 | 4.39 | 2.00 | 2.19x | yes | barrier-dominated |

### `graph`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add_vertex` | small | 32 | 9600000 | 11.09 | 19.58 | 0.57x | yes | - |
| `add_vertex` | medium | 512 | 8960000 | 12.33 | 33.42 | 0.37x | yes | - |
| `add_vertex` | large | 4096 | 10240000 | 17.97 | 50.95 | 0.35x | yes | - |
| `remove_vertex` | small | 32 | 40960000 | 2.93 | 1.34 | 2.19x | yes | barrier-dominated |
| `remove_vertex` | medium | 512 | 320000 | 418.75 | 204.40 | 2.05x | yes | - |
| `remove_vertex` | large | 4096 | 10240 | 12353.52 | 7368.46 | 1.68x | yes | - |
| `add_edge` | small | 32 | 6400000 | 32.66 | 89.56 | 0.36x | yes | - |
| `add_edge` | medium | 512 | 1040000 | 178.85 | 392.35 | 0.46x | yes | - |
| `add_edge` | large | 4096 | 1280000 | 116.80 | 381.89 | 0.31x | yes | - |
| `remove_edge` | small | 32 | 5100000 | 28.04 | 36.51 | 0.77x | yes | - |
| `remove_edge` | medium | 512 | 2560000 | 44.73 | 72.15 | 0.62x | yes | - |
| `remove_edge` | large | 4096 | 1920000 | 56.51 | 121.19 | 0.47x | yes | - |
| `has_vertex` | small | 32 | 6400000 | 25.55 | 19.53 | 1.31x | yes | - |
| `has_vertex` | medium | 512 | 3840000 | 35.55 | 33.67 | 1.06x | yes | - |
| `has_vertex` | large | 4096 | 2560000 | 43.16 | 44.29 | 0.97x | yes | - |
| `has_edge` | small | 32 | 3200000 | 45.00 | 42.34 | 1.06x | yes | - |
| `has_edge` | medium | 512 | 2560000 | 54.10 | 72.80 | 0.74x | yes | - |
| `has_edge` | large | 4096 | 1920000 | 68.23 | 117.00 | 0.58x | yes | - |
| `neighbors` | small | 32 | 5100000 | 30.59 | 21.48 | 1.42x | yes | - |
| `neighbors` | medium | 512 | 2560000 | 50.00 | 38.24 | 1.31x | yes | - |
| `neighbors` | large | 4096 | 1920000 | 62.24 | 62.86 | 0.99x | yes | - |
| `vertices` | small | 32 | 510000 | 253.92 | 34.49 | 7.36x **over** | yes | argument-free |
| `vertices` | medium | 512 | 25500 | 4549.02 | 647.16 | 7.03x **over** | yes | argument-free |
| `vertices` | large | 4096 | 2550 | 38235.29 | 5389.80 | 7.09x **over** | yes | argument-free |
| `edges` | small | 32 | 340000 | 522.06 | 153.76 | 3.40x **over** | yes | argument-free |
| `edges` | medium | 512 | 21000 | 8309.52 | 2870.45 | 2.89x **over** | yes | argument-free |
| `edges` | large | 4096 | 2600 | 75384.62 | 26056.15 | 2.89x **over** | yes | argument-free |
| `new` | small | 32 | 6800000 | 15.51 | 2.35 | 6.59x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 512 | 6400000 | 16.17 | 2.27 | 7.11x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 4096 | 6400000 | 16.56 | 2.34 | 7.09x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 6400000 | 15.70 | 2.26 | 6.94x **over** | yes | argument-free, barrier-dominated |
| `add_vertex` | edge-empty | 0 | 19200000 | 6.02 | 1.35 | 4.46x **over** | yes | barrier-dominated |
| `remove_vertex` | edge-empty | 0 | 76800000 | 1.58 | 1.29 | 1.22x | yes | barrier-dominated |
| `add_edge` | edge-empty | 0 | 64000000 | 1.78 | 1.18 | 1.51x | yes | barrier-dominated |
| `remove_edge` | edge-empty | 0 | 102400000 | 1.85 | 1.24 | 1.49x | yes | barrier-dominated |
| `has_vertex` | edge-empty | 0 | 25600000 | 4.71 | 1.22 | 3.86x **over** | yes | barrier-dominated |
| `has_edge` | edge-empty | 0 | 32000000 | 4.31 | 1.30 | 3.32x **over** | yes | barrier-dominated |
| `neighbors` | edge-empty | 0 | 64000000 | 1.45 | 1.16 | 1.25x | yes | barrier-dominated |
| `vertices` | edge-empty | 0 | - | FAILED | FAILED | - | - | sample 0: A-B = 45000000ns (bend) / 186518000ns (reference), below the 50000000ns / 100000ns minima |
| `edges` | edge-empty | 0 | 12800000 | 12.58 | 4.42 | 2.84x **over** | yes | argument-free |

### `prefix_trie`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 200000 | 727.50 | 149.70 | 4.86x **over** | yes | - |
| `insert` | medium | 2048 | 300000 | 533.33 | 121.14 | 4.40x **over** | yes | - |
| `insert` | large | 32768 | 262144 | 1010.89 | 146.47 | 6.90x **over** | yes | - |
| `lookup` | small | 64 | 400000 | 262.50 | 29.62 | 8.86x **over** | yes | - |
| `lookup` | medium | 2048 | 300000 | 381.67 | 56.89 | 6.71x **over** | yes | - |
| `lookup` | large | 32768 | 340000 | 577.94 | 107.08 | 5.40x **over** | yes | - |
| `remove` | small | 64 | 200000 | 562.50 | 68.96 | 8.16x **over** | yes | restoring pair |
| `remove` | medium | 2048 | 140000 | 753.57 | 103.50 | 7.28x **over** | yes | restoring pair |
| `remove` | large | 32768 | 110000 | 1222.73 | 200.06 | 6.11x **over** | yes | restoring pair |
| `contains` | small | 64 | 700000 | 284.29 | 32.36 | 8.78x **over** | yes | - |
| `contains` | medium | 2048 | 300000 | 385.00 | 57.02 | 6.75x **over** | yes | - |
| `contains` | large | 32768 | 260000 | 515.38 | 102.12 | 5.05x **over** | yes | - |
| `prefix_entries` | small | 64 | 105000 | 1480.95 | 106.19 | 13.95x **over** | yes | - |
| `prefix_entries` | medium | 2048 | 2500 | 50600.00 | 2622.00 | 19.30x **over** | yes | - |
| `prefix_entries` | large | 32768 | 240 | 947916.67 | 35291.67 | 26.86x **over** | yes | - |
| `longest_prefix` | small | 64 | 500000 | 226.00 | 32.21 | 7.02x **over** | yes | - |
| `longest_prefix` | medium | 2048 | 340000 | 320.59 | 61.53 | 5.21x **over** | yes | - |
| `longest_prefix` | large | 32768 | 640000 | 467.97 | 110.93 | 4.22x **over** | yes | - |
| `new` | small | 64 | 153600000 | 1.13 | 2.79 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | medium | 2048 | 166400000 | 1.09 | 2.83 | 0.39x | yes | argument-free, barrier-dominated |
| `new` | large | 32768 | 107100000 | 1.10 | 2.73 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 96000000 | 1.17 | 2.97 | 0.39x | yes | argument-free, barrier-dominated |
| `insert` | edge-empty | 0 | 200000 | 805.00 | 177.81 | 4.53x **over** | yes | - |
| `lookup` | edge-empty | 0 | 700000 | 162.86 | 1.48 | 110.14x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 1200000 | 165.00 | 2.23 | 74.12x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 600000 | 167.50 | 1.56 | 107.14x **over** | yes | barrier-dominated |
| `prefix_entries` | edge-empty | 0 | 6800000 | 22.79 | 4.45 | 5.12x **over** | yes | - |
| `longest_prefix` | edge-empty | 0 | 1200000 | 157.50 | 3.09 | 50.90x **over** | yes | - |

### `queue`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `enqueue` | small | 64 | 13600000 | 7.94 | 1.56 | 5.08x **over** | yes | barrier-dominated |
| `enqueue` | medium | 4096 | 12800000 | 8.05 | 1.55 | 5.21x **over** | yes | barrier-dominated |
| `enqueue` | large | 262144 | 16777216 | 9.75 | 1.72 | 5.66x **over** | yes | barrier-dominated |
| `peek` | small | 64 | 64000000 | 1.58 | 1.31 | 1.21x | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 70400000 | 1.56 | 1.26 | 1.24x | yes | argument-free, barrier-dominated |
| `peek` | large | 262144 | 108800000 | 1.81 | 1.31 | 1.38x | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 153600000 | 1.23 | 3.44 | 0.36x | yes | argument-free |
| `length` | medium | 4096 | 153600000 | 1.21 | 3.53 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 108800000 | 1.21 | 3.50 | 0.35x | yes | argument-free |
| `to_list` | small | 64 | 180000 | 741.67 | 102.81 | 7.21x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 3000 | 34500.00 | 7234.67 | 4.77x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 2430000.00 | 473240.00 | 5.13x **over** | yes | argument-free |
| `dequeue` | small | 64 | 13600000 | 9.12 | 8.58 | 1.06x | yes | restoring pair |
| `dequeue` | medium | 4096 | 15300000 | 8.30 | 8.51 | 0.98x | yes | restoring pair |
| `dequeue` | large | 262144 | 12750000 | 10.78 | 9.68 | 1.11x | yes | restoring pair |
| `new` | small | 64 | 51200000 | 4.19 | 1.54 | 2.72x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 38400000 | 4.34 | 1.65 | 2.62x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 262144 | 30600000 | 3.91 | 1.57 | 2.49x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 38400000 | 3.88 | 1.55 | 2.50x **over** | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 76800000 | 1.21 | 3.51 | 0.35x | yes | argument-free |
| `enqueue` | edge-empty | 0 | 20400000 | 7.60 | 1.63 | 4.67x **over** | yes | barrier-dominated |
| `dequeue` | edge-empty | 0 | 76800000 | 1.46 | 1.48 | 0.99x | yes | barrier-dominated |
| `peek` | edge-empty | 0 | 64000000 | 1.54 | 1.30 | 1.18x | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 20400000 | 7.40 | 1.54 | 4.80x **over** | yes | argument-free, barrier-dominated |

### `segment_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `range_add` | small | 64 | 2600000 | 60.38 | 37.07 | 1.63x | yes | - |
| `range_add` | medium | 4096 | 1360000 | 130.51 | 72.40 | 1.80x | yes | - |
| `range_add` | large | 262144 | 2560000 | 52.54 | 36.20 | 1.45x | yes | - |
| `get` | small | 64 | 6400000 | 31.09 | 3.94 | 7.89x **over** | yes | - |
| `get` | medium | 4096 | 2560000 | 53.71 | 7.52 | 7.14x **over** | yes | - |
| `get` | large | 262144 | 2560000 | 77.73 | 14.11 | 5.51x **over** | yes | - |
| `range_query` | small | 64 | 2550000 | 41.76 | 26.11 | 1.60x | yes | - |
| `range_query` | medium | 4096 | 2040000 | 74.51 | 49.25 | 1.51x | yes | - |
| `range_query` | large | 262144 | 7680000 | 26.43 | 15.46 | 1.71x | yes | - |
| `length` | small | 64 | 102400000 | 1.09 | 2.69 | 0.41x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 96000000 | 1.10 | 2.70 | 0.41x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 108800000 | 1.09 | 2.77 | 0.39x | yes | argument-free, barrier-dominated |
| `set` | small | 64 | 3200000 | 55.62 | 13.55 | 4.10x **over** | yes | - |
| `set` | medium | 4096 | 1040000 | 129.33 | 26.15 | 4.95x **over** | yes | - |
| `set` | large | 262144 | 630000 | 214.29 | 139.87 | 1.53x | yes | - |
| `from_list` | small | 64 | 450000 | 270.00 | 75.31 | 3.59x **over** | yes | - |
| `from_list` | medium | 4096 | 400000 | 277.50 | 75.02 | 3.70x **over** | yes | - |
| `from_list` | large | 262144 | 420000 | 270.24 | 74.54 | 3.63x **over** | yes | - |
| `new` | small | 64 | 12800000 | 12.27 | 13.14 | 0.93x | yes | argument-free |
| `new` | medium | 4096 | 10200000 | 12.30 | 13.27 | 0.93x | yes | argument-free |
| `new` | large | 262144 | 9600000 | 12.29 | 13.45 | 0.91x | yes | argument-free |
| `new` | edge-empty | 0 | 10200000 | 12.35 | 12.77 | 0.97x | yes | argument-free |
| `from_list` | edge-empty | 0 | 400000 | 260.00 | 72.06 | 3.61x **over** | yes | - |
| `length` | edge-empty | 0 | 76800000 | 1.11 | 2.78 | 0.40x | yes | argument-free, barrier-dominated |
| `get` | edge-empty | 0 | 76800000 | 1.37 | 1.22 | 1.12x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 25600000 | 4.32 | 1.28 | 3.37x **over** | yes | barrier-dominated |
| `range_query` | edge-empty | 0 | 15300000 | 9.25 | 2.09 | 4.42x **over** | yes | barrier-dominated |
| `range_add` | edge-empty | 0 | 19200000 | 7.63 | 3.40 | 2.24x | yes | - |

### `union_find`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `find` | small | 64 | 57600000 | 1.88 | 1.64 | 1.15x | yes | barrier-dominated |
| `find` | medium | 4096 | 54400000 | 1.59 | 1.40 | 1.14x | yes | barrier-dominated |
| `find` | large | 65536 | 87040000 | 1.71 | 1.46 | 1.17x | yes | barrier-dominated |
| `union` | small | 64 | 25600000 | 4.98 | 1.90 | 2.62x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 25600000 | 4.38 | 1.60 | 2.73x **over** | yes | barrier-dominated |
| `union` | large | 65536 | - | FAILED | FAILED | - | - | sample 0: A-B = -594000000ns (bend) / 53049000ns (reference), below the 50000000ns / 100000ns minima |
| `connected` | small | 64 | 38400000 | 2.72 | 2.03 | 1.34x | yes | barrier-dominated |
| `connected` | medium | 4096 | 43350000 | 2.54 | 1.73 | 1.47x | yes | barrier-dominated |
| `connected` | large | 65536 | 66560000 | 2.80 | 1.98 | 1.41x | yes | barrier-dominated |
| `component_size` | small | 64 | 57600000 | 1.74 | 1.56 | 1.12x | yes | barrier-dominated |
| `component_size` | medium | 4096 | 108800000 | 1.65 | 1.50 | 1.10x | yes | barrier-dominated |
| `component_size` | large | 65536 | 87040000 | 1.98 | 1.70 | 1.16x | yes | barrier-dominated |
| `component_count` | small | 64 | 89600000 | 1.11 | 3.22 | 0.34x | yes | argument-free |
| `component_count` | medium | 4096 | 108800000 | 1.20 | 3.49 | 0.34x | yes | argument-free |
| `component_count` | large | 65536 | 134400000 | 1.22 | 3.39 | 0.36x | yes | argument-free |
| `new` | small | 64 | 3000000 | 48.50 | 2.48 | 19.58x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 2400000 | 46.04 | 2.32 | 19.86x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 65536 | 3400000 | 47.65 | 2.52 | 18.90x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 2600000 | 49.81 | 2.63 | 18.93x **over** | yes | argument-free, barrier-dominated |
| `find` | edge-empty | 0 | 70400000 | 1.34 | 1.23 | 1.08x | yes | barrier-dominated |
| `union` | edge-empty | 0 | 51200000 | 4.44 | 1.43 | 3.10x **over** | yes | barrier-dominated |
| `connected` | edge-empty | 0 | 51200000 | 1.82 | 1.26 | 1.44x | yes | barrier-dominated |
| `component_size` | edge-empty | 0 | 83200000 | 1.36 | 1.30 | 1.05x | yes | barrier-dominated |
| `component_count` | edge-empty | 0 | 83200000 | 1.10 | 3.18 | 0.35x | yes | argument-free |

## Individual samples

Every sample of every measured row, nanoseconds per operation, in the
order taken (Bend and reference alternate within a row):

```
dynamic_array.push                       small        bend 7.07 8.55 7.70 6.88 6.76 7.42
                                                      ref  4.48 4.46 4.08 4.17 4.12 4.42
dynamic_array.push                       medium       bend 8.20 8.28 9.14 8.12 8.12 7.81
                                                      ref  4.79 4.84 4.88 4.39 4.54 4.54
dynamic_array.push                       large        bend 6.91 10.13 9.00 10.79 9.12 8.76
                                                      ref  6.70 6.30 6.46 5.33 7.79 5.44
dynamic_array.get                        small        bend 2.09 2.09 2.11 2.36 2.07 2.05
                                                      ref  1.68 1.76 1.67 1.72 1.76 1.75
dynamic_array.get                        medium       bend 1.91 2.01 1.96 1.84 1.94 1.88
                                                      ref  1.56 1.71 1.56 1.70 1.68 1.59
dynamic_array.get                        large        bend 2.31 2.06 2.02 2.10 2.23 1.96
                                                      ref  1.64 1.66 1.55 1.70 1.56 1.73
dynamic_array.set                        small        bend 1.86 1.66 1.78 1.75 1.94 1.89
                                                      ref  1.57 1.83 1.75 1.82 1.67 1.73
dynamic_array.set                        medium       bend 1.61 1.65 1.65 1.45 1.61 2.66
                                                      ref  1.55 1.59 1.51 1.70 1.31 3.26
dynamic_array.set                        large        bend 2.63 2.34 2.30 2.23 2.06 2.43
                                                      ref  2.05 2.20 2.08 2.17 2.48 2.30
dynamic_array.length                     small        bend 1.66 1.67 1.66 1.62 1.52 1.70
                                                      ref  4.86 5.35 4.98 4.94 5.63 4.89
dynamic_array.length                     medium       bend 1.70 1.50 1.62 1.63 1.28 1.13
                                                      ref  4.66 4.68 5.00 3.32 3.44 3.43
dynamic_array.length                     large        bend 1.23 1.29 1.31 1.44 1.44 1.24
                                                      ref  3.39 3.73 3.73 3.71 3.83 3.54
dynamic_array.capacity                   small        bend 1.22 1.14 1.30 1.22 1.30 1.29
                                                      ref  2.93 3.29 2.71 3.23 3.34 3.78
dynamic_array.capacity                   medium       bend 1.46 1.29 1.22 1.20 1.22 1.18
                                                      ref  4.06 3.11 3.02 2.99 3.03 3.05
dynamic_array.capacity                   large        bend 1.36 1.19 1.20 1.19 1.23 1.26
                                                      ref  3.06 3.06 3.08 3.03 3.02 2.93
dynamic_array.reserve                    small        bend 4.80 4.84 5.12 4.73 5.27 5.20
                                                      ref  1.53 1.56 1.80 1.62 1.57 1.53
dynamic_array.reserve                    medium       bend 4.84 4.84 4.84 4.73 4.84 4.57
                                                      ref  1.53 1.53 1.53 1.48 1.42 1.53
dynamic_array.reserve                    large        bend 4.87 4.78 4.82 4.91 4.96 4.20
                                                      ref  1.54 1.53 1.32 1.53 1.43 1.53
dynamic_array.to_list                    small        bend 612.50 743.75 662.50 687.50 643.75 825.00
                                                      ref  103.61 103.75 95.96 96.09 103.51 103.80
dynamic_array.to_list                    medium       bend 34000.00 35000.00 37000.00 42000.00 35000.00 40000.00
                                                      ref  6365.00 6085.00 6006.00 6377.67 7088.67 6616.67
dynamic_array.to_list                    large        bend 2380000.00 2240000.00 2400000.00 2440000.00 2240000.00 2440000.00
                                                      ref  501000.00 467160.00 475740.00 425860.00 433720.00 483040.00
dynamic_array.clear                      small        bend 72.69 70.77 70.77 70.77 73.08 74.62
                                                      ref  8.73 8.72 7.64 8.53 8.61 8.72
dynamic_array.clear                      medium       bend 4425.00 3925.00 3575.00 3900.00 3500.00 3625.00
                                                      ref  940.38 665.50 658.42 554.27 688.23 638.95
dynamic_array.clear                      large        bend 238000.00 220000.00 236000.00 228000.00 234000.00 224000.00
                                                      ref  14686.00 14412.00 14882.00 15150.00 15538.00 15080.00
dynamic_array.pop                        small        bend 5.64 5.74 7.21 6.76 6.18 6.18
                                                      ref  4.08 5.84 3.71 4.06 3.84 3.99
dynamic_array.pop                        medium       bend 5.96 5.47 5.60 6.90 4.32 6.09
                                                      ref  4.44 4.08 3.82 3.78 3.18 4.31
dynamic_array.pop                        large        bend 5.19 5.61 4.49 5.19 6.58 7.86
                                                      ref  3.45 3.81 3.70 3.71 3.97 3.92
dynamic_array.new                        small        bend 4.53 5.31 4.65 5.16 4.65 4.88
                                                      ref  3.68 3.04 3.67 3.01 3.29 3.16
dynamic_array.new                        medium       bend 4.10 4.61 4.30 5.20 4.88 5.12
                                                      ref  3.28 3.03 3.28 3.39 3.69 3.09
dynamic_array.new                        large        bend 4.85 5.37 4.68 5.69 5.05 5.71
                                                      ref  3.71 3.34 4.50 3.14 4.02 3.21
dynamic_array.new                        edge-empty   bend 5.82 5.51 4.61 4.96 4.22 4.88
                                                      ref  4.09 3.17 3.76 3.03 3.26 3.14
dynamic_array.length                     edge-empty   bend 1.22 1.22 1.19 1.19 1.18 1.18
                                                      ref  3.45 3.37 3.37 3.50 3.39 3.35
dynamic_array.capacity                   edge-empty   bend 1.18 1.16 1.18 1.13 1.17 1.14
                                                      ref  2.95 3.06 2.94 3.06 3.02 3.06
dynamic_array.get                        edge-empty   bend 1.41 1.45 1.45 1.46 1.48 1.39
                                                      ref  1.30 1.31 1.28 1.32 1.33 1.19
dynamic_array.set                        edge-empty   bend 1.41 1.39 1.74 1.67 1.76 1.38
                                                      ref  1.17 1.61 1.61 1.51 1.41 1.31
dynamic_array.push                       edge-empty   bend 6.62 7.70 7.94 7.75 7.25 6.72
                                                      ref  4.17 4.52 4.47 4.10 4.23 4.14
dynamic_array.pop                        edge-empty   bend 1.32 1.22 1.24 1.20 1.28 1.34
                                                      ref  1.15 1.32 1.23 1.31 1.32 1.35
dynamic_array.reserve                    edge-empty   bend 4.84 4.80 4.65 4.69 4.57 4.53
                                                      ref  1.44 1.44 1.40 1.34 1.44 1.40
dynamic_array.clear                      edge-empty   bend 4.41 4.61 4.26 4.41 4.49 4.26
                                                      ref  2.44 2.36 2.44 2.30 2.45 2.22
dynamic_array.to_list                    edge-empty   bend 5.20 5.59 5.43 5.47 5.20 5.74
                                                      ref  2.40 2.41 2.41 2.38 2.29 2.01
deque.push_front                         small        bend 7.62 6.64 6.13 6.84 6.95 6.64
                                                      ref  1.39 1.76 1.50 1.54 1.54 1.63
deque.push_front                         medium       bend 6.67 6.60 6.93 7.52 7.06 6.99
                                                      ref  1.67 1.65 1.52 1.50 1.51 1.60
deque.push_front                         large        bend 8.38 7.78 7.93 9.35 9.50 7.11
                                                      ref  2.02 1.57 1.73 1.83 1.96 1.71
deque.push_back                          small        bend 7.82 7.31 7.63 7.44 7.31 7.18
                                                      ref  1.53 1.56 1.58 1.54 1.58 1.57
deque.push_back                          medium       bend 7.71 8.39 8.39 8.23 8.59 8.49
                                                      ref  1.55 1.76 1.63 1.74 1.63 1.70
deque.push_back                          large        bend 9.05 6.81 9.80 8.08 8.68 8.30
                                                      ref  1.42 1.64 1.72 1.50 1.88 1.61
deque.peek_front                         small        bend 1.34 1.30 1.22 1.16 1.35 1.32
                                                      ref  1.32 1.37 1.14 1.36 1.31 1.37
deque.peek_front                         medium       bend 1.26 1.22 1.28 1.49 1.33 1.23
                                                      ref  1.31 1.34 1.30 1.45 1.18 1.42
deque.peek_front                         large        bend 1.33 1.18 1.31 1.24 1.28 1.17
                                                      ref  1.28 1.38 1.23 1.33 1.25 1.36
deque.peek_back                          small        bend 1.37 1.15 1.34 1.22 1.32 1.20
                                                      ref  1.29 1.36 1.18 1.36 1.26 1.31
deque.peek_back                          medium       bend 1.44 1.27 1.51 1.24 1.27 1.26
                                                      ref  1.33 1.64 1.66 1.38 1.46 1.33
deque.peek_back                          large        bend 1.30 1.17 1.26 1.23 1.35 1.25
                                                      ref  1.27 1.33 1.26 1.38 1.24 1.36
deque.length                             small        bend 1.37 1.24 1.17 1.20 1.20 1.19
                                                      ref  3.57 3.37 3.34 3.41 3.53 3.36
deque.length                             medium       bend 1.22 1.25 1.18 1.19 1.06 1.20
                                                      ref  3.45 3.45 3.47 3.38 4.10 3.66
deque.length                             large        bend 1.22 1.23 1.23 1.14 1.21 1.23
                                                      ref  3.60 3.34 3.31 3.42 3.58 3.75
deque.to_list                            small        bend 762.50 750.00 706.25 731.25 706.25 731.25
                                                      ref  102.39 110.78 112.52 103.20 102.66 102.97
deque.to_list                            medium       bend 35666.67 39000.00 35000.00 35000.00 37333.33 35333.33
                                                      ref  7230.33 6544.67 7175.67 7014.33 7539.00 7000.67
deque.to_list                            large        bend 2240000.00 2120000.00 2160000.00 2240000.00 2240000.00 2140000.00
                                                      ref  470540.00 417820.00 458240.00 454080.00 485120.00 404080.00
deque.pop_front                          small        bend 5.04 5.59 5.35 5.62 4.61 5.39
                                                      ref  8.57 7.98 8.58 7.72 8.27 7.81
deque.pop_front                          medium       bend 4.65 5.55 4.65 5.47 4.65 5.35
                                                      ref  8.17 8.03 7.97 7.85 8.42 7.99
deque.pop_front                          large        bend 5.94 6.12 5.36 5.67 4.51 5.76
                                                      ref  10.06 7.50 9.36 8.00 8.20 8.24
deque.pop_back                           small        bend 4.96 6.05 4.77 6.21 4.92 5.94
                                                      ref  10.39 7.83 9.15 7.45 9.71 7.46
deque.pop_back                           medium       bend 4.69 5.35 4.41 5.43 4.57 5.16
                                                      ref  8.37 7.67 8.62 7.58 8.36 7.46
deque.pop_back                           large        bend 5.05 5.88 5.20 5.64 4.90 5.15
                                                      ref  8.93 8.16 8.68 7.47 8.46 7.75
deque.new                                small        bend 3.02 3.91 3.93 3.91 3.59 4.09
                                                      ref  1.35 1.43 1.53 1.56 1.56 1.36
deque.new                                medium       bend 3.69 4.22 3.43 3.95 3.99 3.46
                                                      ref  1.33 1.49 1.55 1.55 1.40 1.55
deque.new                                large        bend 3.80 3.63 3.82 4.88 4.27 4.00
                                                      ref  1.45 1.37 1.50 1.76 1.78 1.73
deque.new                                edge-empty   bend 3.85 4.11 3.72 4.04 3.88 4.04
                                                      ref  1.42 1.34 1.49 1.55 1.61 1.55
deque.length                             edge-empty   bend 1.21 1.18 1.20 1.18 1.25 1.22
                                                      ref  3.39 3.47 3.37 3.58 3.47 3.64
deque.push_front                         edge-empty   bend 6.76 6.76 7.21 6.27 6.13 7.25
                                                      ref  1.65 1.62 1.73 1.70 1.57 1.64
deque.push_back                          edge-empty   bend 7.55 7.60 8.04 8.04 7.35 8.33
                                                      ref  1.49 1.71 1.72 1.70 1.72 1.71
deque.pop_front                          edge-empty   bend 1.38 1.22 1.26 1.32 1.28 1.20
                                                      ref  1.30 1.28 1.23 1.27 1.16 1.36
deque.pop_back                           edge-empty   bend 1.26 1.23 1.25 1.24 1.28 1.21
                                                      ref  1.16 1.34 1.25 1.34 1.26 1.35
deque.peek_front                         edge-empty   bend 1.33 1.21 1.28 1.25 1.32 1.12
                                                      ref  1.30 1.35 1.22 1.36 1.21 1.34
deque.peek_back                          edge-empty   bend 1.24 1.63 1.64 1.33 1.35 1.16
                                                      ref  1.56 1.50 1.64 1.34 1.41 1.27
deque.to_list                            edge-empty   bend 7.21 7.35 6.67 8.33 7.45 7.55
                                                      ref  1.49 1.38 1.56 1.50 1.54 1.53
queue.enqueue                            small        bend 8.31 8.68 7.21 7.57 8.90 7.57
                                                      ref  1.58 1.55 1.49 1.56 1.57 1.56
queue.enqueue                            medium       bend 8.75 7.97 8.36 8.12 7.97 7.97
                                                      ref  1.55 1.55 1.40 1.54 1.56 1.54
queue.enqueue                            large        bend 9.78 9.30 9.83 8.29 9.72 10.13
                                                      ref  1.51 1.78 1.66 1.47 1.80 1.87
queue.peek                               small        bend 1.66 1.52 1.55 1.61 1.62 1.55
                                                      ref  1.20 1.34 1.24 1.37 1.28 1.34
queue.peek                               medium       bend 1.59 1.49 1.55 1.53 1.58 1.61
                                                      ref  1.18 1.39 1.20 1.32 1.14 1.34
queue.peek                               large        bend 1.67 1.95 1.86 1.76 1.88 1.54
                                                      ref  1.19 1.42 1.32 1.62 1.30 1.31
queue.length                             small        bend 1.22 1.24 1.24 1.26 1.22 1.20
                                                      ref  3.43 3.73 3.39 3.56 3.36 3.44
queue.length                             medium       bend 1.22 1.20 1.18 1.18 1.42 1.48
                                                      ref  3.57 3.43 3.45 3.65 4.00 3.48
queue.length                             large        bend 1.18 1.19 1.21 1.30 1.28 1.21
                                                      ref  3.49 3.48 3.35 3.76 3.82 3.50
queue.to_list                            small        bend 700.00 811.11 727.78 755.56 727.78 800.00
                                                      ref  102.73 102.98 102.86 103.02 102.76 96.46
queue.to_list                            medium       bend 35666.67 35666.67 34666.67 34333.33 34333.33 34000.00
                                                      ref  6969.33 7300.67 7216.33 7114.00 7282.33 7253.00
queue.to_list                            large        bend 1880000.00 2320000.00 2200000.00 2580000.00 2540000.00 2620000.00
                                                      ref  466260.00 466920.00 479560.00 433800.00 531380.00 494080.00
queue.dequeue                            small        bend 10.96 8.38 10.44 7.57 9.85 7.87
                                                      ref  10.78 7.65 9.48 8.11 9.06 7.46
queue.dequeue                            medium       bend 9.74 6.99 9.48 7.12 9.35 7.25
                                                      ref  9.19 7.78 9.16 7.86 9.35 7.40
queue.dequeue                            large        bend 10.43 11.14 13.33 9.41 11.92 9.10
                                                      ref  11.70 9.74 10.30 8.04 9.61 8.04
queue.new                                small        bend 4.20 4.43 4.18 4.77 3.77 3.89
                                                      ref  1.53 1.38 1.55 1.50 1.60 1.67
queue.new                                medium       bend 3.67 4.95 4.74 3.93 4.38 4.30
                                                      ref  1.75 1.55 1.76 1.47 1.76 1.42
queue.new                                large        bend 3.95 4.08 3.69 4.15 3.50 3.86
                                                      ref  1.63 1.60 1.52 1.36 1.61 1.54
queue.new                                edge-empty   bend 4.53 3.88 3.80 3.88 3.85 4.06
                                                      ref  1.56 1.55 1.55 1.51 1.58 1.40
queue.length                             edge-empty   bend 1.20 1.21 1.25 1.21 1.20 1.22
                                                      ref  3.39 3.80 3.59 3.51 3.51 3.43
queue.enqueue                            edge-empty   bend 7.60 7.50 8.04 7.60 7.55 7.60
                                                      ref  1.51 1.72 1.54 1.70 1.56 1.77
queue.dequeue                            edge-empty   bend 1.24 1.22 1.61 1.46 1.63 1.46
                                                      ref  1.25 1.61 1.49 1.50 1.47 1.34
queue.peek                               edge-empty   bend 1.84 1.53 1.72 1.42 1.55 1.53
                                                      ref  1.30 1.35 1.22 1.38 1.23 1.30
queue.to_list                            edge-empty   bend 7.01 7.65 8.24 7.06 8.04 7.16
                                                      ref  1.41 1.54 1.56 1.72 1.52 1.54
doubly_linked_list.push_front            small        bend 11.86 10.69 11.37 10.49 10.29 10.69
                                                      ref  4.05 4.49 4.72 4.43 4.69 4.44
doubly_linked_list.push_front            medium       bend 10.98 11.57 11.27 11.76 11.18 10.98
                                                      ref  4.12 4.67 4.11 4.64 4.60 4.38
doubly_linked_list.push_front            large        bend 13.54 10.20 12.97 12.30 12.87 13.64
                                                      ref  4.35 3.89 3.93 4.00 4.06 5.17
doubly_linked_list.push_back             small        bend 11.17 10.62 9.92 11.17 9.53 12.81
                                                      ref  4.29 4.58 4.35 4.47 5.14 5.31
doubly_linked_list.push_back             medium       bend 12.60 11.25 10.21 9.79 10.42 11.35
                                                      ref  4.48 4.57 4.33 4.28 4.21 4.08
doubly_linked_list.push_back             large        bend 13.23 14.54 15.38 14.78 14.54 13.11
                                                      ref  5.30 5.32 5.36 5.13 4.10 4.89
doubly_linked_list.insert_before         small        bend 13.04 12.94 13.24 14.22 13.14 11.67
                                                      ref  5.06 4.73 5.30 4.95 5.36 5.39
doubly_linked_list.insert_before         medium       bend 11.47 10.88 10.49 10.00 10.98 11.47
                                                      ref  5.06 4.57 5.21 4.51 4.97 4.57
doubly_linked_list.insert_before         large        bend 18.76 20.82 20.58 14.46 17.64 14.07
                                                      ref  4.97 5.53 7.66 6.35 6.24 5.18
doubly_linked_list.insert_after          small        bend 10.88 15.98 13.14 13.04 12.84 13.73
                                                      ref  4.04 4.98 5.02 5.12 4.61 5.54
doubly_linked_list.insert_after          medium       bend 12.71 13.54 14.27 15.31 15.21 12.81
                                                      ref  6.69 5.28 8.52 6.86 4.02 5.57
doubly_linked_list.insert_after          large        bend 14.31 21.54 20.98 23.44 17.96 17.96
                                                      ref  5.93 7.24 5.86 6.78 5.30 5.18
doubly_linked_list.get                   small        bend 2.08 1.85 2.08 1.99 2.23 2.19
                                                      ref  1.72 1.72 1.59 1.89 1.99 2.01
doubly_linked_list.get                   medium       bend 2.60 2.02 2.16 2.02 1.95 2.19
                                                      ref  1.86 1.81 1.71 1.69 1.73 1.83
doubly_linked_list.get                   large        bend 2.68 2.30 2.16 1.95 2.06 2.48
                                                      ref  1.94 1.75 1.65 1.68 1.59 1.80
doubly_linked_list.set                   small        bend 2.39 1.99 2.23 2.30 2.61 2.28
                                                      ref  1.80 1.95 1.76 2.07 1.94 2.29
doubly_linked_list.set                   medium       bend 2.10 1.92 2.06 1.98 1.92 2.15
                                                      ref  1.66 1.67 1.86 1.49 2.00 1.69
doubly_linked_list.set                   large        bend 2.37 2.11 1.98 2.05 1.95 1.98
                                                      ref  1.83 1.82 1.57 1.61 1.80 1.73
doubly_linked_list.next                  small        bend 2.46 2.86 3.10 2.39 2.48 2.10
                                                      ref  1.97 2.41 2.30 2.13 2.13 1.93
doubly_linked_list.next                  medium       bend 2.48 3.16 3.00 2.44 2.33 2.33
                                                      ref  2.22 2.03 1.91 1.96 1.70 1.83
doubly_linked_list.next                  large        bend 2.58 2.46 2.79 2.73 2.51 2.55
                                                      ref  1.93 2.05 1.95 2.08 2.02 2.07
doubly_linked_list.prev                  small        bend 2.76 2.76 3.70 2.73 2.68 2.32
                                                      ref  2.27 2.73 2.52 2.29 2.30 2.19
doubly_linked_list.prev                  medium       bend 2.52 2.33 2.39 2.19 2.56 2.57
                                                      ref  1.81 1.78 1.90 1.92 1.90 1.90
doubly_linked_list.prev                  large        bend 2.49 2.51 2.67 2.52 3.32 2.49
                                                      ref  2.12 2.04 2.17 2.47 2.06 2.24
doubly_linked_list.length                small        bend 1.32 1.32 1.29 1.21 1.35 1.31
                                                      ref  4.52 3.72 3.72 3.75 4.17 3.70
doubly_linked_list.length                medium       bend 1.42 1.31 1.41 1.29 1.50 1.74
                                                      ref  4.00 3.70 3.99 4.41 4.99 4.23
doubly_linked_list.length                large        bend 1.59 1.62 1.49 1.50 1.53 1.50
                                                      ref  4.16 4.55 3.53 4.48 3.66 3.42
doubly_linked_list.to_list               small        bend 507.69 607.69 630.77 507.69 542.31 730.77
                                                      ref  127.17 110.52 110.73 103.30 110.38 103.42
doubly_linked_list.to_list               medium       bend 13076.92 18589.74 12435.90 17051.28 14487.18 17435.90
                                                      ref  3792.56 3605.77 4205.77 3706.54 3872.31 3792.31
doubly_linked_list.to_list               large        bend 223809.52 330952.38 309523.81 390476.19 414285.71 373809.52
                                                      ref  55733.33 77700.00 91576.19 87833.33 73761.90 72821.43
doubly_linked_list.remove                medium       bend 7.33 9.36 7.51 7.51 6.56 7.81
                                                      ref  6.53 6.98 6.89 6.45 6.68 6.66
doubly_linked_list.remove                large        bend 9.90 8.14 7.04 7.41 8.14 7.23
                                                      ref  7.42 7.35 7.40 7.47 7.66 7.31
doubly_linked_list.new                   small        bend 7.81 8.44 7.89 8.36 7.50 8.59
                                                      ref  2.83 2.60 2.69 2.49 2.80 2.59
doubly_linked_list.new                   medium       bend 8.20 8.67 8.59 8.98 8.91 8.83
                                                      ref  2.81 2.89 2.93 2.83 2.97 2.87
doubly_linked_list.new                   large        bend 8.59 8.52 8.44 8.36 7.81 8.20
                                                      ref  2.89 2.76 2.78 2.54 2.84 2.50
doubly_linked_list.new                   edge-empty   bend 8.18 8.33 7.50 8.33 7.76 8.39
                                                      ref  2.76 2.50 2.84 2.44 2.76 2.52
doubly_linked_list.length                edge-empty   bend 1.00 1.00 1.00 1.03 1.01 0.98
                                                      ref  2.87 2.85 2.85 2.88 2.83 2.85
doubly_linked_list.push_front            edge-empty   bend 7.39 7.32 7.39 7.39 7.45 7.32
                                                      ref  3.12 3.08 3.07 3.03 3.09 3.03
doubly_linked_list.push_back             edge-empty   bend 7.40 7.40 7.24 7.40 7.50 7.34
                                                      ref  3.20 3.06 3.04 3.10 3.04 3.09
doubly_linked_list.insert_before         edge-empty   bend 1.12 1.12 1.12 1.12 1.12 1.14
                                                      ref  1.01 1.01 1.03 1.02 1.02 1.01
doubly_linked_list.insert_after          edge-empty   bend 1.12 1.12 1.11 1.12 1.11 1.14
                                                      ref  1.00 1.01 1.03 1.01 1.00 1.02
doubly_linked_list.remove                edge-empty   bend 1.10 1.12 1.11 1.11 1.11 1.11
                                                      ref  1.01 1.01 1.02 1.01 1.02 1.01
doubly_linked_list.get                   edge-empty   bend 1.11 1.11 1.14 1.11 1.12 1.10
                                                      ref  1.01 1.01 1.04 1.03 1.02 1.03
doubly_linked_list.set                   edge-empty   bend 1.11 1.11 1.11 1.12 1.11 1.10
                                                      ref  1.01 1.02 1.02 1.01 1.02 1.01
doubly_linked_list.next                  edge-empty   bend 1.12 1.11 1.13 1.12 1.13 1.11
                                                      ref  1.02 1.05 1.02 1.02 1.02 1.02
doubly_linked_list.prev                  edge-empty   bend 1.12 1.10 1.10 1.11 1.14 1.11
                                                      ref  1.01 1.01 1.02 1.01 1.01 1.03
doubly_linked_list.to_list               edge-empty   bend 1.88 1.86 1.82 1.86 2.38 1.86
                                                      ref  3.24 3.39 3.42 3.36 3.43 3.44
binary_heap.push                         small        bend 13.98 14.38 14.06 14.30 14.77 14.22
                                                      ref  9.17 9.14 9.23 9.27 9.18 9.15
binary_heap.push                         medium       bend 14.38 14.27 14.17 14.27 14.27 13.96
                                                      ref  9.19 9.14 9.21 9.19 9.19 9.17
binary_heap.push                         large        bend 15.03 15.03 14.81 16.38 15.26 24.23
                                                      ref  8.42 9.21 9.36 9.15 7.11 12.81
binary_heap.peek                         small        bend 1.01 0.99 0.99 0.99 1.00 0.99
                                                      ref  1.00 1.00 1.01 0.55 1.00 1.00
binary_heap.peek                         medium       bend 0.99 0.98 1.00 1.00 0.99 1.00
                                                      ref  1.00 1.00 1.00 0.99 1.00 1.00
binary_heap.peek                         large        bend 0.99 0.99 1.00 1.02 1.04 1.00
                                                      ref  1.00 0.99 1.00 1.03 1.00 0.99
binary_heap.length                       small        bend 0.99 1.01 1.01 1.00 1.00 1.04
                                                      ref  2.85 2.86 2.84 2.85 2.92 2.94
binary_heap.length                       medium       bend 1.31 1.44 1.20 1.01 1.23 1.27
                                                      ref  4.25 2.95 3.23 3.21 4.15 3.16
binary_heap.length                       large        bend 1.39 1.53 1.33 1.85 1.61 1.31
                                                      ref  4.26 3.75 3.57 4.34 4.06 3.30
binary_heap.from_list                    small        bend 136.47 145.88 144.71 184.71 445.88 195.29
                                                      ref  67.59 65.64 92.84 84.36 93.58 78.64
binary_heap.from_list                    medium       bend 201.54 190.77 190.77 198.46 186.15 189.23
                                                      ref  91.64 76.61 91.86 77.02 86.37 79.64
binary_heap.from_list                    large        bend 182.35 180.88 182.35 179.41 183.82 183.82
                                                      ref  153.46 86.92 89.10 80.02 86.12 74.57
binary_heap.to_sorted_list               small        bend 2058.82 1794.12 1926.47 2264.71 1705.88 1676.47
                                                      ref  793.59 838.03 1351.41 865.06 842.65 761.01
binary_heap.to_sorted_list               medium       bend 186666.67 188333.33 205000.00 186666.67 383333.33 150000.00
                                                      ref  76976.67 82898.33 76900.00 75600.00 73706.67 66935.00
binary_heap.to_sorted_list               large        bend 8933333.33 8533333.33 7333333.33 11333333.33 11066666.67 10600000.00
                                                      ref  3744466.67 3794200.00 4822933.33 5182466.67 5497000.00 6240933.33
binary_heap.pop                          small        bend 55.59 56.76 46.47 46.47 48.24 45.00
                                                      ref  20.03 17.85 31.37 20.91 19.99 16.04
binary_heap.pop                          medium       bend 90.00 92.31 86.15 90.77 85.38 90.00
                                                      ref  38.27 37.76 40.06 40.53 40.07 38.00
binary_heap.pop                          large        bend 134.62 134.62 132.69 131.73 136.54 124.04
                                                      ref  50.58 51.77 55.62 52.19 48.17 52.56
binary_heap.new                          small        bend 2.46 4.15 2.75 3.97 2.86 4.27
                                                      ref  3.21 2.90 3.55 2.90 3.40 2.83
binary_heap.new                          medium       bend 2.52 4.02 2.55 3.11 2.75 4.71
                                                      ref  3.35 2.84 3.14 2.76 3.31 3.54
binary_heap.new                          large        bend 3.37 3.65 3.06 3.78 3.19 3.30
                                                      ref  3.31 2.95 3.35 3.10 3.26 3.13
binary_heap.new                          edge-empty   bend 2.64 3.53 2.73 3.56 2.66 3.39
                                                      ref  3.38 2.67 3.18 2.62 3.12 2.79
binary_heap.length                       edge-empty   bend 1.14 1.17 1.10 1.06 1.06 1.11
                                                      ref  3.42 3.10 3.10 3.04 3.09 3.52
binary_heap.push                         edge-empty   bend 19.51 19.22 17.65 17.55 17.45 17.25
                                                      ref  11.97 10.73 11.24 11.04 10.95 11.34
binary_heap.peek                         edge-empty   bend 1.11 1.10 1.10 1.16 1.25 1.19
                                                      ref  1.11 1.11 1.09 1.22 1.17 1.23
binary_heap.pop                          edge-empty   bend 1.21 1.19 1.30 1.12 1.16 1.09
                                                      ref  1.25 1.25 1.21 1.21 1.13 1.19
binary_heap.from_list                    edge-empty   bend 120.00 133.33 123.33 130.00 125.56 131.11
                                                      ref  65.49 52.14 66.27 57.89 68.25 57.80
binary_heap.to_sorted_list               edge-empty   bend 10.23 13.05 11.02 12.81 10.94 12.27
                                                      ref  5.64 5.38 5.54 5.39 5.62 5.01
balanced_search_tree.insert              small        bend 436.67 440.00 446.67 420.00 416.67 433.33
                                                      ref  30.11 29.87 32.17 29.86 30.92 29.33
balanced_search_tree.insert              medium       bend 1140.00 1110.00 1150.00 1340.00 1200.00 1170.00
                                                      ref  77.37 76.67 82.69 87.98 88.41 87.76
balanced_search_tree.insert              large        bend 1850.00 2175.00 1500.00 2275.00 1683.33 1808.33
                                                      ref  184.08 179.01 192.74 190.24 215.57 163.43
balanced_search_tree.remove              small        bend 935.00 900.00 860.00 920.00 920.00 985.00
                                                      ref  73.42 72.58 66.70 69.22 66.66 73.72
balanced_search_tree.remove              medium       bend 1940.00 2180.00 2100.00 2160.00 1920.00 2140.00
                                                      ref  175.78 163.92 168.44 153.04 170.10 150.94
balanced_search_tree.remove              large        bend 2900.00 3116.67 2883.33 3216.67 2216.67 2616.67
                                                      ref  303.95 253.95 266.12 282.37 271.35 266.35
balanced_search_tree.lookup              small        bend 140.00 141.25 138.75 150.00 138.75 161.25
                                                      ref  20.70 20.17 20.67 21.01 22.02 21.08
balanced_search_tree.lookup              medium       bend 333.33 336.67 306.67 323.33 326.67 336.67
                                                      ref  51.82 49.22 53.10 52.40 48.83 52.87
balanced_search_tree.lookup              large        bend 433.33 525.00 481.25 539.58 472.92 614.58
                                                      ref  122.95 112.34 119.47 114.75 104.25 109.53
balanced_search_tree.contains            small        bend 152.86 154.29 148.57 148.57 142.86 165.71
                                                      ref  26.94 22.67 26.38 21.59 27.58 24.67
balanced_search_tree.contains            medium       bend 353.33 338.33 298.33 316.67 315.00 336.67
                                                      ref  49.31 47.15 50.64 50.30 48.35 47.00
balanced_search_tree.contains            large        bend 520.59 538.24 593.14 579.41 472.55 522.55
                                                      ref  116.02 101.40 121.37 102.08 112.24 100.61
balanced_search_tree.min                 small        bend 45.77 46.92 44.23 45.00 44.23 47.69
                                                      ref  1.31 1.29 2.71 1.31 1.32 1.38
balanced_search_tree.min                 medium       bend 138.57 138.57 148.57 120.00 140.00 142.86
                                                      ref  5.26 4.88 4.60 5.12 5.70 5.44
balanced_search_tree.min                 large        bend 138.18 177.27 171.82 179.09 178.18 171.82
                                                      ref  6.35 5.24 6.34 6.57 6.09 5.59
balanced_search_tree.max                 small        bend 46.82 52.27 53.64 50.00 48.18 51.36
                                                      ref  1.32 2.26 1.23 1.31 3.12 1.28
balanced_search_tree.max                 medium       bend 142.50 155.62 143.12 135.62 147.50 142.50
                                                      ref  4.93 4.18 4.56 4.43 3.79 3.67
balanced_search_tree.max                 large        bend 161.88 167.50 168.44 169.38 208.12 175.00
                                                      ref  5.77 4.86 6.08 5.83 5.92 5.46
balanced_search_tree.lower_bound         small        bend 160.00 148.75 143.75 145.00 155.00 155.00
                                                      ref  20.68 19.86 21.79 21.32 21.93 21.35
balanced_search_tree.lower_bound         medium       bend 346.67 346.67 373.33 393.33 370.00 346.67
                                                      ref  52.38 55.97 52.50 51.41 52.76 51.44
balanced_search_tree.lower_bound         large        bend 488.24 626.47 500.00 561.76 414.71 538.24
                                                      ref  110.34 103.71 111.42 100.11 108.07 98.63
balanced_search_tree.range               small        bend 255.21 263.02 265.62 257.81 244.79 255.21
                                                      ref  38.34 40.45 38.80 37.91 36.36 37.92
balanced_search_tree.range               medium       bend 12692.31 13589.74 13461.54 14487.18 13589.74 13333.33
                                                      ref  1072.82 1041.67 1067.05 1124.36 1068.21 1043.85
balanced_search_tree.range               large        bend 119531.25 125781.25 75781.25 130468.75 112500.00 108593.75
                                                      ref  11752.34 9545.31 10964.84 11507.03 9009.38 8817.19
balanced_search_tree.to_list             small        bend 687.50 722.66 714.84 761.72 750.00 792.97
                                                      ref  55.70 55.80 52.85 53.29 55.12 61.95
balanced_search_tree.to_list             medium       bend 66666.67 82000.00 70000.00 62666.67 70666.67 74000.00
                                                      ref  4116.67 4487.33 4442.00 4101.33 4555.33 4468.67
balanced_search_tree.to_list             large        bend 2443137.25 2352941.18 2235294.12 2949019.61 2431372.55 2568627.45
                                                      ref  239023.53 234031.37 307552.94 231984.31 258866.67 306474.51
balanced_search_tree.length              small        bend 1.10 1.12 1.08 1.07 1.08 1.05
                                                      ref  3.21 3.05 3.08 3.10 3.13 3.06
balanced_search_tree.length              medium       bend 1.10 1.16 1.23 1.13 1.11 1.11
                                                      ref  3.11 3.29 3.29 3.17 3.17 3.05
balanced_search_tree.length              large        bend 1.07 1.22 0.89 1.17 1.08 1.12
                                                      ref  3.02 3.05 3.20 2.98 3.25 3.56
balanced_search_tree.new                 small        bend 1.15 1.18 1.21 1.10 1.10 1.16
                                                      ref  2.93 3.03 2.90 2.87 2.79 2.75
balanced_search_tree.new                 medium       bend 1.10 1.11 1.13 1.03 1.07 1.05
                                                      ref  2.73 2.76 2.64 2.75 2.73 2.78
balanced_search_tree.new                 large        bend 1.00 1.16 0.95 1.20 1.08 1.29
                                                      ref  3.13 2.68 3.15 2.75 2.71 3.04
balanced_search_tree.new                 edge-empty   bend 1.17 1.17 1.17 1.11 1.12 1.11
                                                      ref  2.99 2.96 2.80 2.77 2.69 2.76
balanced_search_tree.length              edge-empty   bend 1.10 1.09 1.07 1.12 1.10 1.10
                                                      ref  3.18 3.07 3.16 3.03 3.03 3.34
balanced_search_tree.insert              edge-empty   bend 47.35 47.35 45.59 47.94 43.82 42.35
                                                      ref  3.68 3.34 3.68 3.29 3.69 3.35
balanced_search_tree.remove              edge-empty   bend 7.34 7.76 6.51 7.14 6.98 6.98
                                                      ref  3.11 3.02 3.58 3.23 3.46 3.13
balanced_search_tree.lookup              edge-empty   bend 4.61 4.84 4.53 5.08 4.57 4.65
                                                      ref  1.50 1.40 1.40 1.30 1.40 1.40
balanced_search_tree.contains            edge-empty   bend 4.65 4.61 4.38 4.73 4.30 4.84
                                                      ref  1.41 1.27 1.32 1.40 1.31 1.41
balanced_search_tree.min                 edge-empty   bend 3.79 4.14 3.98 4.49 4.30 4.53
                                                      ref  1.30 1.15 1.22 1.15 1.22 1.30
balanced_search_tree.max                 edge-empty   bend 4.45 4.53 4.49 4.65 4.49 5.12
                                                      ref  1.41 1.30 1.48 1.23 1.44 1.41
balanced_search_tree.lower_bound         edge-empty   bend 6.14 7.25 6.93 7.91 6.54 7.12
                                                      ref  1.63 1.40 1.43 1.55 1.27 1.40
balanced_search_tree.range               edge-empty   bend 5.44 5.29 5.20 5.34 4.95 5.69
                                                      ref  5.49 5.12 5.46 5.30 5.32 4.83
balanced_search_tree.to_list             edge-empty   bend 5.39 5.23 5.00 4.06 5.23 3.79
                                                      ref  4.42 3.89 4.46 3.90 4.29 4.13
bitset.set                               small        bend 1.88 1.86 2.09 2.02 1.95 1.81
                                                      ref  1.66 1.90 1.78 1.80 1.79 1.77
bitset.set                               medium       bend 1.61 1.58 1.55 1.58 1.53 1.56
                                                      ref  1.40 1.40 1.49 1.48 1.40 1.45
bitset.set                               large        bend 1.49 1.56 1.56 1.59 1.49 1.48
                                                      ref  1.41 1.40 1.35 1.39 1.36 1.34
bitset.clear                             small        bend 1.72 1.73 1.80 1.94 2.11 1.94
                                                      ref  1.52 1.71 1.59 1.85 1.74 1.67
bitset.clear                             medium       bend 1.70 1.83 1.78 1.52 1.51 1.56
                                                      ref  1.51 1.51 1.43 1.44 1.49 1.40
bitset.clear                             large        bend 1.56 1.44 1.51 1.52 1.55 1.58
                                                      ref  1.40 1.42 1.28 1.41 1.31 1.49
bitset.get                               small        bend 2.05 1.86 2.05 1.91 1.98 1.83
                                                      ref  1.74 1.79 1.62 1.73 1.62 1.68
bitset.get                               medium       bend 1.82 1.81 1.82 1.84 1.86 1.88
                                                      ref  1.43 1.45 1.44 1.45 1.37 1.42
bitset.get                               large        bend 1.76 1.75 1.76 1.74 1.88 1.91
                                                      ref  1.37 1.46 1.37 1.58 1.52 1.48
bitset.count                             small        bend 64.71 65.29 60.00 70.00 64.12 72.35
                                                      ref  5.05 5.04 5.49 5.10 5.06 4.71
bitset.count                             medium       bend 3725.00 3700.00 3600.00 4100.00 3725.00 4025.00
                                                      ref  230.80 240.78 248.12 235.75 260.15 259.82
bitset.count                             large        bend 256000.00 238000.00 232000.00 218000.00 238000.00 250000.00
                                                      ref  15394.00 15372.00 16588.00 15374.00 15392.00 16568.00
bitset.length                            small        bend 1.10 1.10 1.10 1.16 1.09 1.10
                                                      ref  3.16 3.22 3.32 3.14 3.21 3.49
bitset.length                            medium       bend 1.28 1.33 1.34 1.19 1.20 1.23
                                                      ref  3.65 3.50 3.51 3.39 3.52 3.41
bitset.length                            large        bend 1.13 1.27 1.25 1.13 1.15 1.17
                                                      ref  3.42 3.45 3.46 3.30 3.43 3.22
bitset.to_list                           small        bend 376.47 408.82 385.29 414.71 382.35 414.71
                                                      ref  80.62 84.14 84.21 83.92 81.80 84.12
bitset.to_list                           medium       bend 20333.33 21166.67 20500.00 22333.33 19333.33 21666.67
                                                      ref  5269.67 4926.50 4929.33 4647.83 5013.50 4637.50
bitset.to_list                           large        bend 1840000.00 1890000.00 1790000.00 1980000.00 1910000.00 1910000.00
                                                      ref  332510.00 299570.00 328780.00 306990.00 343670.00 336250.00
bitset.union                             small        bend 6.30 6.88 6.93 6.51 6.93 7.29
                                                      ref  1.32 1.50 1.58 1.65 1.26 1.67
bitset.union                             medium       bend 76.56 74.61 68.75 66.80 66.41 64.45
                                                      ref  66.95 60.29 64.45 60.98 67.58 61.77
bitset.union                             large        bend 3718.75 3718.75 3906.25 3562.50 3656.25 3593.75
                                                      ref  3686.91 3941.66 3649.41 3740.34 3666.78 4024.00
bitset.intersection                      small        bend 6.19 6.31 6.50 6.94 6.44 6.00
                                                      ref  1.29 1.44 1.54 1.63 1.55 1.51
bitset.intersection                      medium       bend 68.14 67.16 65.20 65.69 67.16 77.94
                                                      ref  61.35 57.87 62.73 59.84 62.45 66.12
bitset.intersection                      large        bend 3656.25 3718.75 3750.00 3937.50 3906.25 3875.00
                                                      ref  4049.41 4055.56 4060.06 4193.12 4072.34 3998.41
bitset.difference                        small        bend 7.03 6.88 7.29 6.72 6.98 6.61
                                                      ref  1.37 1.66 1.39 1.36 1.32 1.43
bitset.difference                        medium       bend 73.83 82.03 83.59 78.91 75.78 80.47
                                                      ref  76.76 69.43 69.51 68.03 68.66 69.37
bitset.difference                        large        bend 4187.50 3656.25 3906.25 3875.00 3843.75 3843.75
                                                      ref  3945.50 3988.97 4069.66 3987.38 3884.97 3851.50
bitset.xor                               small        bend 7.12 6.88 6.94 6.81 6.88 6.62
                                                      ref  1.32 1.45 1.69 1.41 1.42 1.65
bitset.xor                               medium       bend 73.44 74.61 66.80 70.31 72.27 75.39
                                                      ref  68.16 67.77 67.17 70.55 68.06 61.87
bitset.xor                               large        bend 3686.27 3921.57 3647.06 3725.49 3725.49 3823.53
                                                      ref  4006.80 4136.82 4015.90 4036.20 4061.51 3934.78
bitset.new                               small        bend 3.49 3.83 3.31 3.54 3.44 3.49
                                                      ref  11.61 13.13 12.23 14.17 12.86 12.51
bitset.new                               medium       bend 3.40 3.56 3.40 3.56 4.25 3.50
                                                      ref  13.12 11.27 13.52 11.75 12.70 12.07
bitset.new                               large        bend 3.50 3.53 3.38 3.47 3.44 3.47
                                                      ref  12.41 11.94 13.32 12.95 11.95 13.43
bitset.new                               edge-empty   bend 3.20 3.36 3.12 3.70 3.49 3.23
                                                      ref  11.91 11.65 11.96 12.34 11.29 12.42
bitset.length                            edge-empty   bend 1.10 1.08 1.13 1.10 1.10 1.10
                                                      ref  3.08 3.25 3.43 3.18 3.13 3.18
bitset.get                               edge-empty   bend 1.33 1.35 1.48 1.38 1.44 1.32
                                                      ref  1.17 1.38 1.26 1.32 1.26 1.34
bitset.set                               edge-empty   bend 1.42 1.28 1.38 1.37 1.45 1.33
                                                      ref  1.22 1.32 1.36 1.34 1.20 1.32
bitset.clear                             edge-empty   bend 1.35 1.34 1.46 1.39 1.54 1.32
                                                      ref  1.32 1.38 1.30 1.35 1.20 1.30
bitset.count                             edge-empty   bend 34.33 35.00 34.00 35.67 33.17 35.50
                                                      ref  4.64 4.26 4.98 4.34 4.45 4.34
bitset.union                             edge-empty   bend 5.86 5.62 5.74 5.12 5.31 5.31
                                                      ref  1.35 1.40 1.29 1.30 1.30 1.30
bitset.intersection                      edge-empty   bend 5.35 5.31 5.04 5.35 5.12 5.16
                                                      ref  1.42 1.18 1.30 1.30 1.34 1.20
bitset.difference                        edge-empty   bend 5.16 6.05 5.86 5.90 5.70 5.27
                                                      ref  1.39 1.40 1.36 1.27 1.29 1.18
bitset.xor                               edge-empty   bend 5.47 5.74 5.35 5.20 5.16 5.59
                                                      ref  1.21 1.30 1.29 1.29 1.36 1.30
bitset.to_list                           edge-empty   bend 38.08 40.00 40.38 40.38 39.23 44.62
                                                      ref  4.19 4.44 4.68 4.20 4.45 4.29
union_find.find                          small        bend 2.00 1.84 1.88 1.89 1.93 1.86
                                                      ref  1.68 1.62 1.57 1.65 1.48 1.65
union_find.find                          medium       bend 1.65 1.58 1.62 1.49 1.53 1.60
                                                      ref  1.40 1.51 1.40 1.37 1.34 1.41
union_find.find                          large        bend 1.79 1.61 1.73 1.69 1.75 1.65
                                                      ref  1.50 1.52 1.40 1.41 1.41 1.54
union_find.union                         small        bend 5.00 4.84 4.96 5.08 4.96 5.08
                                                      ref  1.93 1.84 1.91 1.79 1.89 1.91
union_find.union                         medium       bend 2.27 5.62 3.28 4.65 4.10 8.24
                                                      ref  1.60 1.58 1.61 1.62 1.50 1.69
union_find.connected                     small        bend 2.68 2.50 2.76 2.76 2.92 2.58
                                                      ref  1.81 2.03 2.03 2.06 2.08 1.95
union_find.connected                     medium       bend 2.49 2.65 2.61 2.56 2.51 2.40
                                                      ref  1.73 1.77 1.62 1.86 1.62 1.73
union_find.connected                     large        bend 2.84 2.76 2.88 2.81 2.79 2.75
                                                      ref  1.93 2.09 1.99 1.97 1.95 2.02
union_find.component_size                small        bend 1.81 1.68 1.82 1.72 1.75 1.74
                                                      ref  1.49 1.54 1.53 1.62 1.58 1.57
union_find.component_size                medium       bend 1.60 1.78 1.81 1.53 1.70 1.56
                                                      ref  1.45 1.50 1.51 1.50 1.32 1.50
union_find.component_size                large        bend 1.92 2.25 2.18 2.00 1.96 1.88
                                                      ref  1.55 1.85 1.78 1.67 1.55 1.73
union_find.component_count               small        bend 1.08 1.10 1.14 1.23 1.12 1.09
                                                      ref  3.13 3.26 3.45 3.28 3.18 3.11
union_find.component_count               medium       bend 1.04 1.18 1.29 1.19 1.22 1.26
                                                      ref  3.15 3.68 3.60 3.43 3.49 3.50
union_find.component_count               large        bend 1.21 1.23 1.22 1.29 1.20 1.15
                                                      ref  3.44 3.40 3.44 3.37 3.29 3.03
union_find.new                           small        bend 44.67 49.33 46.00 50.33 48.33 48.67
                                                      ref  2.37 2.42 2.48 2.65 2.62 2.48
union_find.new                           medium       bend 47.92 46.25 45.83 44.17 45.00 49.58
                                                      ref  2.14 2.43 2.55 2.21 2.00 2.53
union_find.new                           large        bend 46.18 48.24 47.65 47.65 47.65 53.24
                                                      ref  2.50 2.92 2.57 2.40 2.39 2.54
union_find.new                           edge-empty   bend 49.23 50.38 49.23 53.08 48.08 51.15
                                                      ref  2.59 2.77 2.61 2.72 2.53 2.65
union_find.find                          edge-empty   bend 1.36 1.35 1.42 1.26 1.32 1.31
                                                      ref  1.23 1.24 1.23 1.18 1.14 1.23
union_find.union                         edge-empty   bend 4.39 4.67 4.75 4.38 4.28 4.49
                                                      ref  1.37 1.47 1.42 1.44 1.45 1.33
union_find.connected                     edge-empty   bend 1.82 1.82 1.80 1.86 1.84 1.76
                                                      ref  1.28 1.29 1.22 1.33 1.24 1.22
union_find.component_size                edge-empty   bend 1.29 1.53 1.49 1.35 1.36 1.37
                                                      ref  1.31 1.34 1.23 1.26 1.30 1.29
union_find.component_count               edge-empty   bend 1.13 1.12 1.03 1.06 1.11 1.09
                                                      ref  3.49 3.18 3.31 3.16 3.18 3.08
fenwick_tree.add                         small        bend 23.91 25.47 24.69 25.16 25.94 29.22
                                                      ref  22.46 23.67 22.33 22.11 22.51 24.09
fenwick_tree.add                         medium       bend 52.69 53.85 54.23 50.77 49.23 46.54
                                                      ref  47.70 47.62 44.60 42.90 46.04 43.74
fenwick_tree.add                         large        bend 69.12 68.63 69.12 69.61 72.55 74.02
                                                      ref  62.34 63.54 61.50 65.96 66.79 67.57
fenwick_tree.prefix_sum                  small        bend 28.24 32.35 31.18 29.12 29.41 28.82
                                                      ref  23.86 24.88 24.63 24.35 23.47 21.91
fenwick_tree.prefix_sum                  medium       bend 47.06 47.45 47.45 47.84 45.49 47.84
                                                      ref  43.45 42.35 43.38 43.13 43.42 47.13
fenwick_tree.prefix_sum                  large        bend 75.78 71.88 73.44 74.22 75.00 73.44
                                                      ref  66.91 62.67 67.62 66.93 66.17 65.95
fenwick_tree.range_sum                   small        bend 27.65 29.02 26.27 27.45 27.65 30.00
                                                      ref  23.40 22.49 24.54 23.33 23.34 22.96
fenwick_tree.range_sum                   medium       bend 50.29 52.65 51.18 52.06 49.41 48.53
                                                      ref  44.46 43.61 44.75 43.66 49.30 43.44
fenwick_tree.range_sum                   large        bend 17.19 16.09 16.09 16.09 16.72 18.12
                                                      ref  14.34 13.71 14.24 14.47 14.74 13.54
fenwick_tree.length                      small        bend 1.14 1.13 1.10 1.10 1.04 1.12
                                                      ref  3.57 3.19 3.25 3.05 3.08 3.14
fenwick_tree.length                      medium       bend 1.23 1.12 1.11 1.05 1.07 1.05
                                                      ref  3.48 3.20 3.23 3.10 3.20 3.10
fenwick_tree.length                      large        bend 1.04 1.05 1.10 1.21 1.13 1.10
                                                      ref  3.17 3.13 3.19 3.20 3.23 3.07
fenwick_tree.from_list                   small        bend 162.67 158.00 163.33 152.00 135.33 140.00
                                                      ref  35.35 29.57 30.65 27.21 26.82 27.08
fenwick_tree.from_list                   medium       bend 137.50 162.50 155.83 159.17 160.00 156.67
                                                      ref  30.21 28.96 29.74 31.46 31.53 29.98
fenwick_tree.from_list                   large        bend 146.15 145.19 147.12 143.27 142.31 143.27
                                                      ref  27.98 26.85 26.68 26.98 29.48 27.02
fenwick_tree.new                         small        bend 8.09 7.50 7.40 7.50 7.30 8.38
                                                      ref  13.32 11.99 12.77 12.21 15.15 12.20
fenwick_tree.new                         medium       bend 7.50 7.45 7.35 7.40 7.06 8.48
                                                      ref  12.12 11.91 12.29 12.00 12.62 12.60
fenwick_tree.new                         large        bend 7.50 7.19 6.69 7.19 7.25 7.94
                                                      ref  12.24 15.85 11.86 12.12 11.44 12.74
fenwick_tree.new                         edge-empty   bend 7.66 7.42 7.03 7.73 7.50 7.81
                                                      ref  13.60 18.09 11.69 11.85 13.00 12.48
fenwick_tree.from_list                   edge-empty   bend 148.57 144.29 147.14 142.86 144.29 161.43
                                                      ref  28.53 28.12 31.41 27.24 25.80 27.80
fenwick_tree.length                      edge-empty   bend 1.16 1.13 1.11 1.11 1.07 1.05
                                                      ref  3.24 3.13 3.08 3.04 3.14 3.03
fenwick_tree.add                         edge-empty   bend 1.81 2.28 2.16 2.23 2.00 2.11
                                                      ref  1.29 1.42 1.36 1.40 1.47 1.32
fenwick_tree.prefix_sum                  edge-empty   bend 2.43 2.24 2.38 2.25 2.32 2.23
                                                      ref  1.27 1.29 1.29 1.27 1.26 1.22
fenwick_tree.range_sum                   edge-empty   bend 4.30 4.49 4.30 4.69 4.22 4.77
                                                      ref  2.05 1.66 1.96 1.69 2.09 2.09
segment_tree.range_add                   small        bend 58.46 60.38 65.38 62.69 60.38 60.38
                                                      ref  38.40 35.27 37.43 36.70 39.21 36.17
segment_tree.range_add                   medium       bend 128.68 147.06 130.88 124.26 130.15 133.09
                                                      ref  70.62 74.22 75.85 74.18 69.60 70.25
segment_tree.range_add                   large        bend 52.73 57.42 51.17 52.34 52.34 54.30
                                                      ref  40.19 34.92 36.60 37.05 34.16 35.80
segment_tree.get                         small        bend 32.03 30.31 31.25 30.94 31.25 29.22
                                                      ref  3.59 4.03 3.85 4.03 3.77 4.04
segment_tree.get                         medium       bend 54.30 52.34 55.47 53.12 54.69 53.12
                                                      ref  7.52 7.52 7.54 7.51 7.53 7.53
segment_tree.get                         large        bend 77.34 75.78 80.08 74.61 78.12 80.08
                                                      ref  13.78 14.63 13.89 14.98 13.74 14.33
segment_tree.range_query                 small        bend 39.22 40.39 41.57 45.88 42.75 41.96
                                                      ref  26.96 25.94 26.28 25.91 26.85 24.90
segment_tree.range_query                 medium       bend 74.02 74.02 75.49 74.51 75.00 74.51
                                                      ref  49.12 49.20 49.92 49.21 49.43 49.29
segment_tree.range_query                 large        bend 27.21 30.60 27.99 25.65 24.35 23.96
                                                      ref  18.55 15.63 16.46 14.89 15.28 13.91
segment_tree.length                      small        bend 1.15 1.09 1.11 1.05 1.09 1.04
                                                      ref  2.91 2.59 2.66 2.72 2.60 2.81
segment_tree.length                      medium       bend 1.18 1.11 1.05 1.09 1.07 1.24
                                                      ref  2.76 2.63 2.69 2.65 2.70 2.83
segment_tree.length                      large        bend 1.07 1.07 1.08 1.20 1.14 1.09
                                                      ref  2.71 2.76 2.78 2.79 2.87 2.76
segment_tree.set                         small        bend 50.62 53.75 55.94 57.19 61.56 55.31
                                                      ref  12.47 13.22 12.63 14.87 13.89 14.26
segment_tree.set                         medium       bend 138.46 130.77 127.88 120.19 125.00 139.42
                                                      ref  27.14 26.74 26.81 25.57 25.38 25.42
segment_tree.set                         large        bend 198.41 228.57 195.24 223.81 204.76 223.81
                                                      ref  118.50 141.44 142.06 127.38 153.99 138.29
segment_tree.from_list                   small        bend 266.67 266.67 275.56 302.22 273.33 257.78
                                                      ref  76.05 76.62 75.53 72.84 70.79 75.09
segment_tree.from_list                   medium       bend 292.50 272.50 255.00 260.00 282.50 285.00
                                                      ref  82.74 74.52 101.06 75.51 73.50 72.83
segment_tree.from_list                   large        bend 261.90 285.71 261.90 269.05 271.43 271.43
                                                      ref  73.95 86.33 76.89 71.82 71.39 75.12
segment_tree.new                         small        bend 12.19 12.27 12.03 12.27 12.42 12.42
                                                      ref  13.26 12.98 13.27 13.02 17.04 12.81
segment_tree.new                         medium       bend 12.25 12.35 12.35 12.35 11.27 12.16
                                                      ref  13.27 13.27 13.71 13.07 14.21 12.83
segment_tree.new                         large        bend 11.88 12.08 12.81 12.92 12.50 12.08
                                                      ref  11.72 13.51 13.86 13.51 13.14 13.38
segment_tree.new                         edge-empty   bend 12.35 12.35 12.35 12.45 11.67 12.16
                                                      ref  13.31 12.70 12.61 12.04 12.90 12.84
segment_tree.from_list                   edge-empty   bend 270.00 237.50 262.50 250.00 257.50 265.00
                                                      ref  74.59 69.53 69.36 66.84 76.07 79.11
segment_tree.length                      edge-empty   bend 1.11 1.03 1.12 1.15 1.16 1.09
                                                      ref  2.82 2.74 2.70 3.00 2.88 2.71
segment_tree.get                         edge-empty   bend 1.35 1.37 1.38 1.28 1.39 1.38
                                                      ref  1.20 1.24 1.18 1.29 1.19 1.32
segment_tree.set                         edge-empty   bend 4.38 4.45 4.18 4.30 4.34 4.10
                                                      ref  1.33 1.32 1.32 1.25 1.18 1.24
segment_tree.range_query                 edge-empty   bend 9.22 8.82 9.35 9.74 9.28 8.89
                                                      ref  2.14 2.16 1.97 2.09 2.09 1.87
segment_tree.range_add                   edge-empty   bend 7.29 7.08 7.45 7.81 8.02 8.02
                                                      ref  3.19 3.72 3.49 3.31 3.17 3.60
prefix_trie.insert                       small        bend 680.00 825.00 825.00 665.00 650.00 775.00
                                                      ref  151.37 148.04 161.28 173.50 141.72 139.01
prefix_trie.insert                       medium       bend 513.33 560.00 526.67 536.67 536.67 530.00
                                                      ref  128.64 116.94 130.62 117.11 118.61 123.67
prefix_trie.insert                       large        bend 656.13 1224.52 728.61 1235.96 797.27 1358.03
                                                      ref  145.20 147.73 194.04 182.78 136.12 137.38
prefix_trie.lookup                       small        bend 270.00 252.50 255.00 270.00 255.00 277.50
                                                      ref  29.61 29.62 29.62 29.20 31.59 27.72
prefix_trie.lookup                       medium       bend 370.00 376.67 370.00 386.67 396.67 416.67
                                                      ref  55.87 53.30 57.48 57.50 61.74 56.30
prefix_trie.lookup                       large        bend 529.41 623.53 594.12 579.41 500.00 576.47
                                                      ref  98.44 108.49 112.55 105.67 120.05 99.62
prefix_trie.remove                       small        bend 510.00 550.00 545.00 600.00 575.00 585.00
                                                      ref  75.65 67.94 68.98 73.39 68.94 68.31
prefix_trie.remove                       medium       bend 742.86 800.00 814.29 764.29 700.00 714.29
                                                      ref  106.22 103.71 103.30 97.13 110.38 96.24
prefix_trie.remove                       large        bend 836.36 1245.45 918.18 1427.27 1200.00 1418.18
                                                      ref  190.68 189.11 200.00 200.13 206.29 212.88
prefix_trie.contains                     small        bend 300.00 271.43 278.57 282.86 308.57 285.71
                                                      ref  33.51 31.00 33.15 32.02 32.70 31.78
prefix_trie.contains                     medium       bend 443.33 390.00 350.00 386.67 383.33 370.00
                                                      ref  60.25 55.78 58.55 58.22 55.40 55.82
prefix_trie.contains                     large        bend 411.54 557.69 469.23 569.23 484.62 546.15
                                                      ref  100.66 95.08 109.69 99.47 103.58 109.49
prefix_trie.prefix_entries               small        bend 1295.24 1857.14 1476.19 1666.67 1438.10 1485.71
                                                      ref  105.42 101.85 110.66 106.95 108.62 105.30
prefix_trie.prefix_entries               medium       bend 44800.00 52800.00 50800.00 52800.00 48000.00 50400.00
                                                      ref  2618.40 2629.60 2394.40 2625.60 2913.20 2427.20
prefix_trie.prefix_entries               large        bend 745833.33 970833.33 854166.67 925000.00 970833.33 1162500.00
                                                      ref  38212.50 34600.00 36583.33 32362.50 35983.33 31387.50
prefix_trie.longest_prefix               small        bend 218.00 228.00 226.00 240.00 218.00 226.00
                                                      ref  32.24 31.60 32.50 30.30 32.45 32.17
prefix_trie.longest_prefix               medium       bend 311.76 320.59 320.59 332.35 311.76 367.65
                                                      ref  60.64 60.75 62.31 59.85 65.96 65.61
prefix_trie.longest_prefix               large        bend 467.19 579.69 485.94 412.50 467.19 468.75
                                                      ref  140.71 120.31 110.73 111.14 105.81 96.90
prefix_trie.new                          small        bend 1.10 1.07 1.07 1.21 1.24 1.16
                                                      ref  2.66 2.70 2.65 3.01 2.99 2.88
prefix_trie.new                          medium       bend 1.09 1.05 1.06 1.10 1.22 1.13
                                                      ref  2.71 2.76 2.67 3.16 3.00 2.90
prefix_trie.new                          large        bend 1.24 1.15 1.08 1.07 1.06 1.12
                                                      ref  2.97 2.73 2.77 2.65 2.73 2.70
prefix_trie.new                          edge-empty   bend 1.06 1.16 1.27 1.20 1.18 1.16
                                                      ref  2.68 3.11 3.06 2.90 3.05 2.83
prefix_trie.insert                       edge-empty   bend 755.00 855.00 750.00 995.00 640.00 985.00
                                                      ref  188.76 177.56 186.57 173.50 178.05 163.68
prefix_trie.lookup                       edge-empty   bend 174.29 154.29 145.71 160.00 165.71 170.00
                                                      ref  1.44 1.52 1.52 1.44 1.44 1.51
prefix_trie.remove                       edge-empty   bend 162.50 156.67 165.83 164.17 173.33 166.67
                                                      ref  2.06 2.17 2.18 2.27 2.32 2.31
prefix_trie.contains                     edge-empty   bend 183.33 156.67 170.00 173.33 165.00 146.67
                                                      ref  1.62 1.61 1.27 1.51 1.61 1.51
prefix_trie.prefix_entries               edge-empty   bend 25.29 22.65 21.32 22.94 22.06 24.85
                                                      ref  4.47 4.45 4.45 4.45 4.65 4.18
prefix_trie.longest_prefix               edge-empty   bend 169.17 165.00 164.17 140.83 148.33 150.83
                                                      ref  3.11 3.11 3.09 2.91 3.10 2.91
graph.add_vertex                         small        bend 10.94 11.15 10.94 11.04 11.67 12.08
                                                      ref  19.61 18.44 17.70 20.16 20.36 19.55
graph.add_vertex                         medium       bend 11.38 12.28 11.27 12.50 12.83 12.39
                                                      ref  33.63 31.28 33.22 35.17 35.04 31.34
graph.add_vertex                         large        bend 16.89 19.82 16.60 18.36 18.75 17.58
                                                      ref  49.68 47.31 50.56 55.08 51.33 55.64
graph.remove_vertex                      small        bend 2.78 3.54 3.34 2.56 3.08 2.78
                                                      ref  1.42 1.27 1.41 1.40 1.03 1.28
graph.remove_vertex                      medium       bend 281.25 431.25 275.00 656.25 406.25 446.88
                                                      ref  216.10 223.57 192.71 163.52 171.58 323.85
graph.remove_vertex                      large        bend 10546.88 12988.28 11425.78 14453.12 11718.75 13671.88
                                                      ref  8718.55 6627.44 7391.41 7419.63 7345.51 7231.84
graph.add_edge                           small        bend 31.72 33.91 32.50 32.81 31.72 35.00
                                                      ref  92.91 87.65 91.47 87.23 91.92 87.64
graph.add_edge                           medium       bend 173.08 182.69 181.73 186.54 175.96 165.38
                                                      ref  415.90 392.23 400.27 386.25 392.47 357.17
graph.add_edge                           large        bend 108.59 115.62 132.03 124.22 117.97 115.62
                                                      ref  358.79 454.37 441.88 378.03 385.75 361.61
graph.remove_edge                        small        bend 28.63 28.04 27.45 29.41 26.67 28.04
                                                      ref  39.43 36.48 36.54 34.86 36.92 35.66
graph.remove_edge                        medium       bend 42.58 44.53 44.92 47.27 44.53 48.44
                                                      ref  71.70 69.44 72.60 69.46 75.87 82.02
graph.remove_edge                        large        bend 53.12 64.58 56.77 56.25 53.12 57.81
                                                      ref  123.06 114.75 119.48 122.90 135.72 114.53
graph.has_vertex                         small        bend 25.78 25.31 26.41 25.31 25.94 24.53
                                                      ref  18.07 20.17 20.02 21.31 18.87 19.03
graph.has_vertex                         medium       bend 38.28 38.02 36.72 33.33 33.85 34.38
                                                      ref  35.59 35.80 34.67 32.64 32.67 32.54
graph.has_vertex                         large        bend 44.14 42.97 43.36 42.97 42.19 46.09
                                                      ref  44.10 44.92 44.11 44.47 43.78 48.72
graph.has_edge                           small        bend 45.62 51.56 48.75 43.75 44.38 40.94
                                                      ref  41.77 45.03 45.68 39.82 41.95 42.72
graph.has_edge                           medium       bend 57.42 54.30 52.73 53.91 52.73 61.72
                                                      ref  71.97 70.71 67.75 73.63 74.32 79.39
graph.has_edge                           large        bend 67.71 74.48 68.75 69.79 67.71 65.10
                                                      ref  123.58 115.96 127.07 110.81 118.03 110.49
graph.neighbors                          small        bend 30.00 30.00 31.18 30.78 30.39 37.06
                                                      ref  22.36 20.68 21.21 20.25 22.47 21.75
graph.neighbors                          medium       bend 52.34 50.00 47.66 48.44 52.73 50.00
                                                      ref  37.83 37.12 38.65 39.00 39.12 37.09
graph.neighbors                          large        bend 60.42 67.71 65.10 61.98 60.94 62.50
                                                      ref  65.97 63.81 64.02 59.91 58.86 61.92
graph.vertices                           small        bend 256.86 239.22 258.82 268.63 250.98 233.33
                                                      ref  37.15 34.82 33.79 33.51 37.09 34.15
graph.vertices                           medium       bend 4000.00 4274.51 4470.59 4627.45 4627.45 5137.25
                                                      ref  606.59 650.39 766.16 645.92 648.39 618.71
graph.vertices                           large        bend 38431.37 39215.69 37647.06 39607.84 38039.22 36470.59
                                                      ref  4987.45 5546.67 5497.65 5445.88 5333.73 5172.94
graph.edges                              small        bend 517.65 585.29 514.71 514.71 526.47 567.65
                                                      ref  153.77 142.54 175.45 152.43 172.63 153.74
graph.edges                              medium       bend 7857.14 8428.57 7333.33 8761.90 8571.43 8190.48
                                                      ref  2899.62 2841.29 3233.05 3090.52 2809.95 2813.05
graph.edges                              large        bend 65000.00 76923.08 80769.23 80384.62 68461.54 73846.15
                                                      ref  27861.15 26993.46 27556.15 24140.77 25118.85 22995.00
graph.new                                small        bend 14.71 17.06 15.59 15.44 13.68 16.03
                                                      ref  2.27 2.44 2.27 2.18 2.62 2.44
graph.new                                medium       bend 16.25 15.31 15.47 16.72 16.09 17.19
                                                      ref  2.27 2.26 2.28 2.12 2.45 2.45
graph.new                                large        bend 16.09 17.03 17.19 15.47 14.69 17.19
                                                      ref  2.46 2.40 2.28 2.15 2.43 2.25
graph.new                                edge-empty   bend 14.69 16.25 16.09 17.50 15.31 15.31
                                                      ref  2.48 2.26 2.26 2.23 2.26 2.11
graph.add_vertex                         edge-empty   bend 5.94 6.15 5.21 5.73 6.09 6.15
                                                      ref  1.29 1.33 1.35 1.40 1.35 1.40
graph.remove_vertex                      edge-empty   bend 1.64 1.54 1.61 1.46 1.63 1.48
                                                      ref  1.30 1.30 1.29 1.32 1.19 1.16
graph.add_edge                           edge-empty   bend 1.77 1.73 1.88 1.80 1.92 1.70
                                                      ref  1.19 1.16 1.13 1.20 1.17 1.27
graph.remove_edge                        edge-empty   bend 1.80 1.75 1.74 1.94 1.97 1.89
                                                      ref  1.23 1.19 1.15 1.29 1.25 1.24
graph.has_vertex                         edge-empty   bend 4.69 4.65 4.38 5.16 4.73 4.84
                                                      ref  1.22 1.23 1.22 1.21 1.23 1.14
graph.has_edge                           edge-empty   bend 4.31 4.31 4.22 4.38 4.22 4.34
                                                      ref  1.30 1.30 1.43 1.28 1.35 1.29
graph.neighbors                          edge-empty   bend 1.45 1.53 1.44 1.48 1.44 1.44
                                                      ref  1.16 1.16 1.16 1.15 1.16 1.19
graph.edges                              edge-empty   bend 12.66 12.50 12.34 12.89 12.81 11.80
                                                      ref  4.48 4.45 4.55 4.40 4.14 3.87
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
doubly_linked_list.remove / small: sample 1: A-B = 37000000ns (bend) / 113091000ns (reference), below the 50000000ns / 100000ns minima
union_find.union / large: sample 0: A-B = -594000000ns (bend) / 53049000ns (reference), below the 50000000ns / 100000ns minima
graph.vertices / edge-empty: sample 0: A-B = 45000000ns (bend) / 186518000ns (reference), below the 50000000ns / 100000ns minima
```

Raw per-sample log: `build/bench/logs/samples.log`;
machine-readable evidence with source and artifact hashes:
`build/performance/report.json`.
