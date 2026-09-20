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

For a *size-changing* operation the `k` operations that `A - B` isolates are
the ones between the `k`-th and the `2k`-th of a round, so they run at sizes
`size + k .. size + 2k` (or `size - k .. size - 2k`) rather than at `size ..
size + k`. Both sides do exactly that, from the identical starting structure
and the identical argument stream, so the comparison stays same-algorithm and
same-workload; the row's `size` is the size the round was *built* to, as
before.

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
  reference side** (thousands of `clock_gettime` ticks), with a x3 headroom so
  run-to-run variation cannot push a sample below the minimum.
* **How the batch grows matters.** For a *size-preserving* operation the batch
  grows in `count` - more operations inside one round - so the structure is
  still built exactly `reps` times and a large structure with a cheap
  operation stays measurable. For a *size-changing* operation (push, pop,
  insert, remove, clear, reserve) only whole rounds may be repeated, because a
  longer batch would no longer be that operation at that size.
  `benchmarks/workloads.py` classifies every operation and the classification
  is recorded per row (`grow`).
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

Neither flag changes the verdict: it rests on the many rows with a varying
argument and a reference cost well above the barrier.

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

Two of the structures - `dynamic_array` and `bitset` - are backed by native
`Base.Array`, which is a **linear** flat array with O(1) indexed read and
write: they are threaded (every operation returns the structure) and updated
in place, exactly like their C references. The other ten are **persistent**:
an update returns a new value and shares what it did not have to rebuild,
because that is what the proofs are about and what the language's runtime
provides for `Data` types. The C references implement the **same algorithm**
with the same asymptotics but mutate and reuse nodes in place, because that is
what an optimized C implementation of that algorithm does; each reference
header says so explicitly. Concretely:

| structure | Bend representation | C reference | why the comparison is still same-algorithm |
|---|---|---|---|
| `dynamic_array` | `Base.Array` perfect binary tree of slots, doubling | flat `realloc`ed buffer, doubling | identical growth policy and amortised bounds; the tree is Base's array, not a different algorithm |
| `deque`, `queue` | two lists with a half-split rebalance | ring buffer | both amortised O(1) at both ends |
| `doubly_linked_list` | ordered map from id to `{value, prev, next}` | arena of node records + the same ordered map | identical handle semantics (ids never reused, stale/foreign rejected) |
| `binary_heap` | complete binary tree, sift up/down | flat array heap, same sift | identical sift order |
| `balanced_search_tree` | red-black binary tree, Okasaki insert, functional delete fixup | the same red-black algorithm, nodes reused in place (`benchmarks/native/redblack.h`) | identical rotations, identical fixup cases, identical order |
| `bitset` | native `Base.Array` of U32 words (linear, O(1) indexed access) | flat U32 array | identical packed-word representation and identical word operations |
| `union_find` | three parallel `Base.Array` arenas (roots, sizes, member lists) indexed by element | flat array of cells, union by size | identical union-by-size relinking |
| `fenwick_tree`, `segment_tree` | perfect binary trees with lazy tags | flat arrays with the same recursion | identical index arithmetic |
| `prefix_trie` | sibling lists ordered by code | the same sibling lists | identical traversal |
| `graph` | ordered map to ordered neighbour sets | the same two ordered maps | identical adjacency representation |

For the ten persistent structures the Bend side therefore pays for allocating
the nodes on the path it rebuilds where the C side overwrites them. That is a
property of the representation the proofs are about, not a handicap added to
the benchmark: the C reference is the fastest reasonable implementation of the
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

## What the primitives cost

Measured by `tools/costmodel.py` from `benchmarks/micro.bend` and
`benchmarks/native/micro.c`, which perform the identical work. This is not
one of the contract workloads; it is here so the per-operation ratios below
can be read against what the primitives themselves cost.

| primitive | operations | bend ns | ref ns | ratio |
|---|---|---|---|---|
| `arith` - one LCG step and an add | 20000000 | 1.40 | 1.54 | 0.91x |
| `array` - one indexed read + write of a 4096-slot `Base.Array` | 20000000 | 1.55 | 1.46 | 1.06x |
| `list` - one step of traversing a **retained** (`&2`) cons list | 20480000 | 9.03 | 1.05 | 8.62x |
| `alloc` - one node of a built-and-consumed binary `Data` tree | 40955000 | 2.64 | 22.17 | 0.12x |
| `fresh` - one node of a built-and-consumed (`&2`) cons list | 20480000 | 10.89 | 16.50 | 0.66x |

Read it carefully, because it does not say what one might expect:

* **Arithmetic and indexed array access are at parity.** Bend compiles
  `Array.get` / `Array.set` to real indexed loads and stores on a flat
  array, and compiles `Nat`, `U32.from_nat`/`to_nat` and `Nat.div` to
  machine arithmetic. None of that is folklore: it is measured here, and
  it stays flat across sizes 64 .. 262144 in the `dynamic_array.get` and
  `bitset.get` rows below.
* **Allocation is not the problem.** A plain `Data` tree node costs Bend
  about 2.6 ns to allocate, traverse and release.
* **Traversing a retained, shareable (`&2`) structure is the problem.**
  Walking a cons list that stays alive costs Bend ~9 ns per node against
  ~1 ns in C, because the runtime has to duplicate the part it consumes.
  Every persistent structure in this library is built from `&2` types, so
  every traversal pays it. That single factor, not allocation, is what
  separates the passing rows from the failing ones.

The two C rows that look bad for C (`alloc`, `fresh`) are malloc/free per
node, which is what a straightforward C linked structure does; an arena
would be several times faster. They are **not** presented as Bend wins -
they are here to show what Bend node allocation costs in absolute terms.

That is why the structures divide so sharply below: an **array-backed**
structure (`dynamic_array`, and now `bitset`) can meet the 2.5x contract,
and a structure whose operations walk retained `&2` nodes cannot, whatever
the constant factors. Closing the remaining gap is a representation change
for each structure (indices into a `Base.Array` arena instead of shared
node references), with the proofs redone against it - not tuning.
`WORK_LOG.md` lists them in priority order.

One structure has already been moved: `bitset` kept its packed words in
a cons list, which made `get`/`set`/`clear` O(words) while the C
reference is O(1) on a flat array - not the same algorithm. It now uses
`Base.Array`. `WORK_LOG.md` records the before/after per row (for
example `bitset.set` at size 4096 went from 2243x to the figure in the
table below) and what the migration cost in proof terms.

## Verdict

| | rows |
|---|---|
| measured, within 2.5x | 130 |
| measured, **over 2.5x** | 260 |
| of those, unflagged (varying argument, reference > 3 ns/op) | 134 |
| FAILED measurement (not resolvable above the clock minima) | 18 |
| total rows in `benchmarks/workloads.py` | 408 |

**The 2.5x contract is NOT met.** 260 measured workloads exceed it
(worst unflagged row: `segment_tree.get` / large at **35.91x**;
worst row of any kind: `prefix_trie.contains` / edge-empty at **110.93x**)
and 18 workloads could not be measured at all. The nine `lru.*`
operations the contract requires have **no rows**: the retained LRU
cannot be compiled to a native binary with this toolchain (see
`docs/VALIDATION.md`, "arity over 255"), and substituting a
non-native backend would not be a native-C measurement.

## All rows

`bend` and `ref` are nanoseconds per operation (median of the samples).

### `balanced_search_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 300000 | 471.67 | 38.75 | 12.17x **over** | yes | - |
| `insert` | medium | 4096 | 100000 | 1185.00 | 133.60 | 8.87x **over** | yes | - |
| `insert` | large | 131072 | 60000 | 2241.67 | 241.71 | 9.27x **over** | yes | - |
| `remove` | small | 64 | 19200000 | 7.73 | 1.40 | 5.51x **over** | yes | barrier-dominated |
| `remove` | medium | 4096 | - | FAILED | FAILED | - | - | sample 0: A-B = 49000000ns (bend) / 30100000ns (reference), below the 50000000ns / 100000ns minima |
| `remove` | large | 131072 | - | FAILED | FAILED | - | - | sample 3: A-B = -1356000000ns (bend) / 59198000ns (reference), below the 50000000ns / 100000ns minima |
| `lookup` | small | 64 | 1000000 | 115.00 | 16.61 | 6.92x **over** | yes | - |
| `lookup` | medium | 4096 | 450000 | 243.33 | 37.24 | 6.53x **over** | yes | - |
| `lookup` | large | 131072 | 520000 | 395.19 | 85.16 | 4.64x **over** | yes | - |
| `contains` | small | 64 | 1600000 | 111.56 | 17.35 | 6.43x **over** | yes | - |
| `contains` | medium | 4096 | 800000 | 244.38 | 38.25 | 6.39x **over** | yes | - |
| `contains` | large | 131072 | 520000 | 399.04 | 85.95 | 4.64x **over** | yes | - |
| `min` | small | 64 | 5200000 | 35.19 | 1.03 | 34.28x **over** | yes | argument-free, barrier-dominated |
| `min` | medium | 4096 | 1800000 | 108.06 | 3.78 | 28.58x **over** | yes | argument-free |
| `min` | large | 131072 | 1050000 | 178.57 | 6.50 | 27.49x **over** | yes | argument-free |
| `max` | small | 64 | 4400000 | 42.84 | 1.08 | 39.56x **over** | yes | argument-free, barrier-dominated |
| `max` | medium | 4096 | 1000000 | 106.50 | 3.80 | 28.03x **over** | yes | argument-free |
| `max` | large | 131072 | 2550000 | 139.02 | 4.26 | 32.66x **over** | yes | argument-free |
| `lower_bound` | small | 64 | 900000 | 110.56 | 16.48 | 6.71x **over** | yes | - |
| `lower_bound` | medium | 4096 | 400000 | 256.25 | 36.50 | 7.02x **over** | yes | - |
| `lower_bound` | large | 131072 | 680000 | 420.59 | 84.79 | 4.96x **over** | yes | - |
| `range` | small | 64 | 640000 | 209.38 | 31.35 | 6.68x **over** | yes | - |
| `range` | medium | 4096 | 15300 | 9673.20 | 784.54 | 12.33x **over** | yes | - |
| `range` | large | 131072 | 1280 | 87109.38 | 8132.81 | 10.71x **over** | yes | - |
| `to_list` | small | 64 | 204000 | 573.53 | 42.44 | 13.51x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 2100 | 51428.57 | 3282.14 | 15.67x **over** | yes | argument-free |
| `to_list` | large | 131072 | 85 | 1894117.65 | 190641.18 | 9.94x **over** | yes | argument-free |
| `length` | small | 64 | 102400000 | 1.00 | 2.80 | 0.36x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 108800000 | 1.00 | 2.76 | 0.36x | yes | argument-free, barrier-dominated |
| `length` | large | 131072 | 144000000 | 0.99 | 2.74 | 0.36x | yes | argument-free, barrier-dominated |
| `new` | small | 64 | 204800000 | 0.97 | 2.39 | 0.41x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 102400000 | 0.96 | 2.40 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | large | 131072 | 163200000 | 0.98 | 2.40 | 0.41x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 108800000 | 0.96 | 2.38 | 0.40x | yes | argument-free, barrier-dominated |
| `length` | edge-empty | 0 | 134400000 | 0.96 | 2.70 | 0.36x | yes | argument-free, barrier-dominated |
| `insert` | edge-empty | 0 | 3400000 | 32.06 | 1.49 | 21.58x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 25600000 | 5.06 | 1.00 | 5.08x **over** | yes | barrier-dominated |
| `lookup` | edge-empty | 0 | 32000000 | 3.28 | 1.00 | 3.29x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 32000000 | 3.31 | 1.00 | 3.31x **over** | yes | barrier-dominated |
| `min` | edge-empty | 0 | 32000000 | 3.28 | 1.00 | 3.29x **over** | yes | argument-free, barrier-dominated |
| `max` | edge-empty | 0 | 32000000 | 3.28 | 1.00 | 3.28x **over** | yes | argument-free, barrier-dominated |
| `lower_bound` | edge-empty | 0 | 25600000 | 4.73 | 1.00 | 4.74x **over** | yes | barrier-dominated |
| `range` | edge-empty | 0 | 25600000 | 4.20 | 3.80 | 1.11x | yes | - |
| `to_list` | edge-empty | 0 | 25600000 | 4.12 | 3.35 | 1.23x | yes | argument-free |

### `binary_heap`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 6400000 | 481.72 | 90.04 | 5.35x **over** | yes | - |
| `push` | medium | 4096 | 2550000 | 394.31 | 59.06 | 6.68x **over** | yes | - |
| `push` | large | 131072 | - | FAILED | FAILED | - | - | a single Bend region already takes 33838ms at count=20000 reps=128 while A-B is only -3235000000ns, so the row cannot be sampled 6 times within the per-row budget |
| `peek` | small | 64 | 38400000 | 3.93 | 1.49 | 2.63x **over** | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 32000000 | 4.34 | 1.70 | 2.55x **over** | yes | argument-free, barrier-dominated |
| `peek` | large | 131072 | 108800000 | 3.66 | 1.46 | 2.51x **over** | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 153600000 | 1.27 | 3.59 | 0.35x | yes | argument-free |
| `length` | medium | 4096 | 76800000 | 1.31 | 3.99 | 0.33x | yes | argument-free |
| `length` | large | 131072 | 160000000 | 1.12 | 3.50 | 0.32x | yes | argument-free |
| `from_list` | small | 64 | 400000 | 275.00 | 49.34 | 5.57x **over** | yes | - |
| `from_list` | medium | 4096 | 700000 | 286.43 | 45.89 | 6.24x **over** | yes | - |
| `from_list` | large | 131072 | 1280000 | 279.69 | 42.95 | 6.51x **over** | yes | - |
| `to_sorted_list` | small | 64 | 8000 | 17500.00 | 1218.56 | 14.36x **over** | yes | argument-free |
| `to_sorted_list` | medium | 4096 | 100 | 2765000.00 | 289575.00 | 9.55x **over** | yes | argument-free |
| `to_sorted_list` | large | 131072 | 5 | 162600000.00 | 37936100.00 | 4.29x **over** | yes | argument-free |
| `pop` | small | 64 | 655360 | 195.31 | 27.03 | 7.23x **over** | yes | - |
| `pop` | medium | 4096 | - | FAILED | FAILED | - | - | sample 1: A-B = 42000000ns (bend) / 9313000ns (reference), below the 50000000ns / 100000ns minima |
| `pop` | large | 131072 | 131072 | 1010.89 | 190.04 | 5.32x **over** | yes | - |
| `new` | small | 64 | 153600000 | 1.18 | 2.95 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 89600000 | 1.28 | 2.94 | 0.43x | yes | argument-free, barrier-dominated |
| `new` | large | 131072 | 204800000 | 1.11 | 2.99 | 0.37x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 166400000 | 1.22 | 3.03 | 0.40x | yes | argument-free |
| `length` | edge-empty | 0 | 153600000 | 1.22 | 3.49 | 0.35x | yes | argument-free |
| `push` | edge-empty | 0 | 3400000 | 403.53 | 70.12 | 5.75x **over** | yes | - |
| `peek` | edge-empty | 0 | 32000000 | 3.59 | 1.30 | 2.76x **over** | yes | argument-free, barrier-dominated |
| `pop` | edge-empty | 0 | 25600000 | 4.24 | 1.30 | 3.26x **over** | yes | barrier-dominated |
| `from_list` | edge-empty | 0 | 400000 | 283.75 | 49.89 | 5.69x **over** | yes | - |
| `to_sorted_list` | edge-empty | 0 | 20400000 | 5.66 | 5.05 | 1.12x | yes | argument-free |

### `bitset`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `set` | small | 64 | 76800000 | 1.44 | 1.28 | 1.13x | yes | barrier-dominated |
| `set` | medium | 4096 | 153600000 | 1.32 | 1.17 | 1.13x | yes | barrier-dominated |
| `set` | large | 262144 | 83200000 | 1.30 | 1.15 | 1.13x | yes | barrier-dominated |
| `clear` | small | 64 | 76800000 | 1.45 | 1.27 | 1.14x | yes | barrier-dominated |
| `clear` | medium | 4096 | 76800000 | 1.29 | 1.15 | 1.12x | yes | barrier-dominated |
| `clear` | large | 262144 | 134400000 | 1.29 | 1.15 | 1.12x | yes | barrier-dominated |
| `get` | small | 64 | 76800000 | 1.59 | 1.32 | 1.21x | yes | barrier-dominated |
| `get` | medium | 4096 | 76800000 | 1.48 | 1.19 | 1.25x | yes | barrier-dominated |
| `get` | large | 262144 | 108800000 | 1.48 | 1.18 | 1.26x | yes | barrier-dominated |
| `count` | small | 64 | 2550000 | 49.22 | 3.89 | 12.67x **over** | yes | argument-free |
| `count` | medium | 4096 | 40000 | 2950.00 | 184.64 | 15.98x **over** | yes | argument-free |
| `count` | large | 262144 | 1000 | 179500.00 | 11870.50 | 15.12x **over** | yes | argument-free |
| `length` | small | 64 | 115200000 | 0.99 | 2.75 | 0.36x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 108800000 | 0.98 | 2.73 | 0.36x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 108800000 | 0.98 | 2.70 | 0.36x | yes | argument-free, barrier-dominated |
| `to_list` | small | 64 | 340000 | 298.53 | 64.53 | 4.63x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 6000 | 17000.00 | 4020.33 | 4.23x **over** | yes | argument-free |
| `to_list` | large | 262144 | 100 | 1485000.00 | 258560.00 | 5.74x **over** | yes | argument-free |
| `union` | small | 64 | 22400000 | 4.89 | 1.02 | 4.80x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 2560000 | 52.34 | 48.67 | 1.08x | yes | - |
| `union` | large | 262144 | 51000 | 2754.90 | 2883.89 | 0.96x | yes | - |
| `intersection` | small | 64 | 22400000 | 4.96 | 1.13 | 4.40x **over** | yes | barrier-dominated |
| `intersection` | medium | 4096 | 2560000 | 54.30 | 49.04 | 1.11x | yes | - |
| `intersection` | large | 262144 | 64000 | 2765.62 | 2889.09 | 0.96x | yes | - |
| `difference` | small | 64 | 22400000 | 5.00 | 1.05 | 4.77x **over** | yes | barrier-dominated |
| `difference` | medium | 4096 | 2040000 | 54.41 | 49.68 | 1.10x | yes | - |
| `difference` | large | 262144 | 64000 | 2835.94 | 2962.22 | 0.96x | yes | - |
| `xor` | small | 64 | 22400000 | 4.96 | 1.01 | 4.88x **over** | yes | barrier-dominated |
| `xor` | medium | 4096 | 2560000 | 55.08 | 48.49 | 1.14x | yes | - |
| `xor` | large | 262144 | 51000 | 2774.51 | 2881.77 | 0.96x | yes | - |
| `new` | small | 64 | 25600000 | 4.69 | 9.18 | 0.51x | yes | argument-free |
| `new` | medium | 4096 | 30600000 | 4.69 | 9.17 | 0.51x | yes | argument-free |
| `new` | large | 262144 | 22400000 | 4.69 | 9.18 | 0.51x | yes | argument-free |
| `new` | edge-empty | 0 | 25600000 | 4.73 | 8.74 | 0.54x | yes | argument-free |
| `length` | edge-empty | 0 | 102400000 | 1.00 | 2.79 | 0.36x | yes | argument-free, barrier-dominated |
| `get` | edge-empty | 0 | 179200000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 102400000 | 1.12 | 1.01 | 1.11x | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 102400000 | 1.12 | 1.01 | 1.10x | yes | barrier-dominated |
| `count` | edge-empty | 0 | 4200000 | 24.64 | 3.42 | 7.22x **over** | yes | argument-free |
| `union` | edge-empty | 0 | 25600000 | 4.22 | 1.00 | 4.23x **over** | yes | barrier-dominated |
| `intersection` | edge-empty | 0 | 30600000 | 4.22 | 0.99 | 4.24x **over** | yes | barrier-dominated |
| `difference` | edge-empty | 0 | 25600000 | 4.22 | 0.99 | 4.24x **over** | yes | barrier-dominated |
| `xor` | edge-empty | 0 | 25600000 | 4.41 | 0.99 | 4.44x **over** | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 6000000 | 30.92 | 3.41 | 9.08x **over** | yes | argument-free |

### `deque`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 10400000 | 11.92 | 3.40 | 3.50x **over** | yes | - |
| `push_front` | medium | 4096 | 12800000 | 11.52 | 3.43 | 3.36x **over** | yes | - |
| `push_front` | large | 262144 | - | FAILED | FAILED | - | - | sample 5: A-B = 37000000ns (bend) / 12498000ns (reference), below the 50000000ns / 100000ns minima |
| `push_back` | small | 64 | 10400000 | 12.50 | 1.70 | 7.37x **over** | yes | barrier-dominated |
| `push_back` | medium | 4096 | 10200000 | 11.72 | 1.61 | 7.27x **over** | yes | barrier-dominated |
| `push_back` | large | 262144 | - | FAILED | FAILED | - | - | sample 5: A-B = 1294000000ns (bend) / -7518000ns (reference), below the 50000000ns / 100000ns minima |
| `peek_front` | small | 64 | 25600000 | 5.94 | 1.54 | 3.86x **over** | yes | argument-free, barrier-dominated |
| `peek_front` | medium | 4096 | 19200000 | 5.42 | 1.43 | 3.78x **over** | yes | argument-free, barrier-dominated |
| `peek_front` | large | 262144 | 19200000 | 5.94 | 1.49 | 3.99x **over** | yes | argument-free, barrier-dominated |
| `peek_back` | small | 64 | 20400000 | 5.98 | 1.56 | 3.83x **over** | yes | argument-free, barrier-dominated |
| `peek_back` | medium | 4096 | 19200000 | 5.81 | 1.44 | 4.03x **over** | yes | argument-free, barrier-dominated |
| `peek_back` | large | 262144 | 20400000 | 5.56 | 1.45 | 3.85x **over** | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 76800000 | 1.21 | 3.10 | 0.39x | yes | argument-free |
| `length` | medium | 4096 | 166400000 | 1.24 | 3.16 | 0.39x | yes | argument-free |
| `length` | large | 262144 | 86700000 | 1.21 | 3.02 | 0.40x | yes | argument-free |
| `to_list` | small | 64 | 140000 | 910.71 | 112.99 | 8.06x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 2000 | 69000.00 | 6970.25 | 9.90x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 4690000.00 | 417640.00 | 11.23x **over** | yes | argument-free |
| `pop_front` | small | 64 | 6684672 | 21.54 | 6.19 | 3.48x **over** | yes | - |
| `pop_front` | medium | 4096 | 5505024 | 30.52 | 5.39 | 5.67x **over** | yes | - |
| `pop_front` | large | 262144 | 5505024 | 26.52 | 4.80 | 5.52x **over** | yes | - |
| `pop_back` | small | 64 | - | FAILED | FAILED | - | - | A-B stayed at -1471000000ns (bend) / 178248000ns (reference) at the round cap count=32 reps=4194304 (bend region A 6430ms), below the 50000000ns / 100000ns minima |
| `pop_back` | medium | 4096 | - | FAILED | FAILED | - | - | a single Bend region already takes 21645ms at count=2048 reps=192512 while A-B is only -812000000ns, so the row cannot be sampled 6 times within the per-row budget |
| `pop_back` | large | 262144 | - | FAILED | FAILED | - | - | sample 0: A-B = -84000000ns (bend) / 768430000ns (reference), below the 50000000ns / 100000ns minima |
| `new` | small | 64 | 89600000 | 1.19 | 3.00 | 0.40x | yes | argument-free |
| `new` | medium | 4096 | 89600000 | 1.22 | 3.04 | 0.40x | yes | argument-free |
| `new` | large | 262144 | 130050000 | 1.23 | 3.17 | 0.39x | yes | argument-free |
| `new` | edge-empty | 0 | 76800000 | 1.24 | 3.09 | 0.40x | yes | argument-free |
| `length` | edge-empty | 0 | 89600000 | 1.23 | 3.03 | 0.41x | yes | argument-free |
| `push_front` | edge-empty | 0 | 13600000 | 11.62 | 3.36 | 3.46x **over** | yes | - |
| `push_back` | edge-empty | 0 | 10400000 | 12.21 | 1.71 | 7.13x **over** | yes | barrier-dominated |
| `pop_front` | edge-empty | 0 | 10200000 | 9.85 | 2.57 | 3.84x **over** | yes | barrier-dominated |
| `pop_back` | edge-empty | 0 | 12800000 | 9.45 | 2.48 | 3.82x **over** | yes | barrier-dominated |
| `peek_front` | edge-empty | 0 | 10200000 | 10.39 | 2.68 | 3.88x **over** | yes | argument-free, barrier-dominated |
| `peek_back` | edge-empty | 0 | 13600000 | 9.82 | 2.63 | 3.73x **over** | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 12800000 | 8.05 | 1.54 | 5.21x **over** | yes | argument-free, barrier-dominated |

### `doubly_linked_list`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push_front` | small | 64 | 100000 | 4245.00 | 243.62 | 17.43x **over** | yes | - |
| `push_front` | medium | 2048 | 50000 | 3980.00 | 197.83 | 20.12x **over** | yes | - |
| `push_front` | large | 32768 | 40000 | 3925.00 | 190.44 | 20.61x **over** | yes | - |
| `push_back` | small | 64 | 100000 | 4400.00 | 256.88 | 17.13x **over** | yes | - |
| `push_back` | medium | 2048 | 50000 | 4140.00 | 211.05 | 19.62x **over** | yes | - |
| `push_back` | large | 32768 | 40000 | 6550.00 | 238.51 | 27.46x **over** | yes | - |
| `insert_before` | small | 64 | 100000 | 6150.00 | 373.10 | 16.48x **over** | yes | - |
| `insert_before` | medium | 2048 | 50000 | 5800.00 | 369.28 | 15.71x **over** | yes | - |
| `insert_before` | large | 32768 | 20000 | 5600.00 | 497.33 | 11.26x **over** | yes | - |
| `insert_after` | small | 64 | 100000 | 6220.00 | 443.43 | 14.03x **over** | yes | - |
| `insert_after` | medium | 2048 | 50000 | 5750.00 | 401.04 | 14.34x **over** | yes | - |
| `insert_after` | large | 32768 | 20000 | 5875.00 | 477.15 | 12.31x **over** | yes | - |
| `get` | small | 64 | 400000 | 246.25 | 32.41 | 7.60x **over** | yes | - |
| `get` | medium | 2048 | 400000 | 442.50 | 62.36 | 7.10x **over** | yes | - |
| `get` | large | 32768 | 140000 | 871.43 | 175.57 | 4.96x **over** | yes | - |
| `set` | small | 64 | 200000 | 842.50 | 31.93 | 26.38x **over** | yes | - |
| `set` | medium | 2048 | 100000 | 1635.00 | 63.04 | 25.94x **over** | yes | - |
| `set` | large | 32768 | 60000 | 2400.00 | 173.50 | 13.83x **over** | yes | - |
| `next` | small | 64 | 500000 | 225.00 | 32.72 | 6.88x **over** | yes | - |
| `next` | medium | 2048 | 250000 | 432.00 | 63.05 | 6.85x **over** | yes | - |
| `next` | large | 32768 | 280000 | 708.93 | 180.04 | 3.94x **over** | yes | - |
| `prev` | small | 64 | 500000 | 222.00 | 32.14 | 6.91x **over** | yes | - |
| `prev` | medium | 2048 | 250000 | 444.00 | 62.94 | 7.05x **over** | yes | - |
| `prev` | large | 32768 | 160000 | 706.25 | 169.05 | 4.18x **over** | yes | - |
| `length` | small | 64 | 20400000 | 5.49 | 3.82 | 1.44x | yes | argument-free |
| `length` | medium | 2048 | 38400000 | 5.89 | 3.99 | 1.48x | yes | argument-free |
| `length` | large | 32768 | 26880000 | 5.97 | 3.74 | 1.60x | yes | argument-free |
| `to_list` | small | 64 | 10000 | 14700.00 | 278.70 | 52.74x **over** | yes | argument-free |
| `to_list` | medium | 2048 | 300 | 863333.33 | 26280.00 | 32.85x **over** | yes | argument-free |
| `to_list` | large | 32768 | 20 | 19350000.00 | 1362550.00 | 14.20x **over** | yes | argument-free |
| `remove` | small | 64 | 208896 | 1206.34 | 53.18 | 22.68x **over** | yes | - |
| `remove` | medium | 2048 | 69632 | 2441.41 | 125.30 | 19.48x **over** | yes | - |
| `remove` | large | 32768 | 32768 | 3402.71 | 325.94 | 10.44x **over** | yes | - |
| `new` | small | 64 | 70400000 | 1.60 | 3.94 | 0.41x | yes | argument-free |
| `new` | medium | 2048 | 83200000 | 1.39 | 3.47 | 0.40x | yes | argument-free |
| `new` | large | 32768 | - | FAILED | FAILED | - | - | sample 0: A-B = 48000000ns (bend) / 252449000ns (reference), below the 50000000ns / 100000ns minima |
| `new` | edge-empty | 0 | 64000000 | 1.39 | 3.48 | 0.40x | yes | argument-free |
| `length` | edge-empty | 0 | 102400000 | 1.44 | 3.49 | 0.41x | yes | argument-free |
| `push_front` | edge-empty | 0 | 100000 | 6530.00 | 362.04 | 18.04x **over** | yes | - |
| `push_back` | edge-empty | 0 | 100000 | 6660.00 | 396.64 | 16.79x **over** | yes | - |
| `insert_before` | edge-empty | 0 | 6400000 | 16.88 | 1.92 | 8.79x **over** | yes | barrier-dominated |
| `insert_after` | edge-empty | 0 | 10200000 | 15.34 | 1.71 | 8.99x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 6400000 | 15.94 | 1.96 | 8.15x **over** | yes | barrier-dominated |
| `get` | edge-empty | 0 | 10200000 | 13.97 | 1.73 | 8.07x **over** | yes | barrier-dominated |
| `set` | edge-empty | 0 | 10200000 | 13.82 | 1.71 | 8.06x **over** | yes | barrier-dominated |
| `next` | edge-empty | 0 | 20400000 | 6.57 | 1.72 | 3.82x **over** | yes | barrier-dominated |
| `prev` | edge-empty | 0 | 20400000 | 6.52 | 1.71 | 3.81x **over** | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 12800000 | 8.44 | 5.17 | 1.63x | yes | argument-free |

### `dynamic_array`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `push` | small | 64 | 5200000 | 23.27 | 3.58 | 6.50x **over** | yes | - |
| `push` | medium | 4096 | 10200000 | 19.41 | 3.25 | 5.97x **over** | yes | - |
| `push` | large | 262144 | - | FAILED | FAILED | - | - | sample 2: A-B = -91000000ns (bend) / 26414000ns (reference), below the 50000000ns / 100000ns minima |
| `get` | small | 64 | 51200000 | 2.17 | 1.83 | 1.19x | yes | barrier-dominated |
| `get` | medium | 4096 | 64000000 | 1.89 | 1.62 | 1.17x | yes | barrier-dominated |
| `get` | large | 262144 | 54400000 | 2.17 | 1.63 | 1.33x | yes | barrier-dominated |
| `set` | small | 64 | 64000000 | 1.85 | 1.81 | 1.02x | yes | barrier-dominated |
| `set` | medium | 4096 | 64000000 | 1.58 | 1.53 | 1.03x | yes | barrier-dominated |
| `set` | large | 262144 | 107100000 | 1.77 | 1.71 | 1.04x | yes | barrier-dominated |
| `length` | small | 64 | 76800000 | 1.26 | 3.37 | 0.37x | yes | argument-free |
| `length` | medium | 4096 | 96000000 | 1.24 | 3.62 | 0.34x | yes | argument-free |
| `length` | large | 262144 | 134400000 | 1.26 | 3.62 | 0.35x | yes | argument-free |
| `capacity` | small | 64 | 20400000 | 6.50 | 3.49 | 1.86x | yes | argument-free |
| `capacity` | medium | 4096 | 15300000 | 10.23 | 3.47 | 2.95x **over** | yes | argument-free |
| `capacity` | large | 262144 | 9600000 | 12.81 | 3.50 | 3.66x **over** | yes | argument-free |
| `reserve` | small | 64 | 6800000 | 22.50 | 1.59 | 14.16x **over** | yes | barrier-dominated |
| `reserve` | medium | 4096 | 6800000 | 24.04 | 1.66 | 14.45x **over** | yes | barrier-dominated |
| `reserve` | large | 262144 | 2550000 | 33.14 | 1.84 | 18.01x **over** | yes | barrier-dominated |
| `to_list` | small | 64 | 100000 | 1140.00 | 104.01 | 10.96x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 2000 | 92750.00 | 6060.25 | 15.30x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 6470000.00 | 494640.00 | 13.08x **over** | yes | argument-free |
| `clear` | small | 64 | 1700000 | 64.12 | 7.96 | 8.06x **over** | yes | - |
| `clear` | medium | 4096 | 40000 | 3800.00 | 584.80 | 6.50x **over** | yes | - |
| `clear` | large | 262144 | 500 | 251000.00 | 12846.00 | 19.54x **over** | yes | - |
| `pop` | small | 64 | - | FAILED | FAILED | - | - | sample 0: A-B = -243000000ns (bend) / 130340000ns (reference), below the 50000000ns / 100000ns minima |
| `pop` | medium | 4096 | - | FAILED | FAILED | - | - | sample 3: A-B = -642000000ns (bend) / 418200000ns (reference), below the 50000000ns / 100000ns minima |
| `pop` | large | 262144 | - | FAILED | FAILED | - | - | sample 0: A-B = -89000000ns (bend) / 325008000ns (reference), below the 50000000ns / 100000ns minima |
| `new` | small | 64 | 25600000 | 4.79 | 3.39 | 1.41x | yes | argument-free |
| `new` | medium | 4096 | 25600000 | 5.02 | 3.49 | 1.44x | yes | argument-free |
| `new` | large | 262144 | 22950000 | 4.95 | 3.31 | 1.49x | yes | argument-free |
| `new` | edge-empty | 0 | 25600000 | 4.94 | 3.25 | 1.52x | yes | argument-free |
| `length` | edge-empty | 0 | 153600000 | 1.17 | 3.39 | 0.35x | yes | argument-free |
| `capacity` | edge-empty | 0 | 25600000 | 4.39 | 3.22 | 1.37x | yes | argument-free |
| `get` | edge-empty | 0 | 76800000 | 1.65 | 1.55 | 1.06x | yes | barrier-dominated |
| `set` | edge-empty | 0 | 64000000 | 1.51 | 1.37 | 1.10x | yes | barrier-dominated |
| `push` | edge-empty | 0 | 6800000 | 19.12 | 3.04 | 6.29x **over** | yes | - |
| `pop` | edge-empty | 0 | 76800000 | 1.28 | 1.28 | 1.00x | yes | barrier-dominated |
| `reserve` | edge-empty | 0 | 10400000 | 18.70 | 1.57 | 11.93x **over** | yes | barrier-dominated |
| `clear` | edge-empty | 0 | 25600000 | 4.69 | 2.43 | 1.93x | yes | barrier-dominated |
| `to_list` | edge-empty | 0 | 12800000 | 8.91 | 2.34 | 3.81x **over** | yes | argument-free, barrier-dominated |

### `fenwick_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add` | small | 64 | 2400000 | 73.75 | 19.07 | 3.87x **over** | yes | - |
| `add` | medium | 4096 | 550000 | 200.00 | 37.08 | 5.39x **over** | yes | - |
| `add` | large | 262144 | 1020000 | 448.04 | 51.48 | 8.70x **over** | yes | - |
| `prefix_sum` | small | 64 | 1700000 | 58.53 | 19.12 | 3.06x **over** | yes | - |
| `prefix_sum` | medium | 4096 | 750000 | 148.00 | 35.47 | 4.17x **over** | yes | - |
| `prefix_sum` | large | 262144 | 1280000 | 333.59 | 51.59 | 6.47x **over** | yes | - |
| `range_sum` | small | 64 | 3000000 | 63.83 | 19.71 | 3.24x **over** | yes | - |
| `range_sum` | medium | 4096 | 650000 | 153.08 | 36.49 | 4.20x **over** | yes | - |
| `range_sum` | large | 262144 | 1280000 | 70.70 | 12.08 | 5.85x **over** | yes | - |
| `length` | small | 64 | 115200000 | 1.01 | 2.89 | 0.35x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 134400000 | 1.01 | 2.89 | 0.35x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 108800000 | 0.97 | 2.86 | 0.34x | yes | argument-free, barrier-dominated |
| `from_list` | small | 64 | 300000 | 396.67 | 22.40 | 17.71x **over** | yes | - |
| `from_list` | medium | 4096 | 300000 | 393.33 | 22.88 | 17.19x **over** | yes | - |
| `from_list` | large | 262144 | 1280000 | 402.73 | 22.93 | 17.56x **over** | yes | - |
| `new` | small | 64 | 61200000 | 3.86 | 9.99 | 0.39x | yes | argument-free |
| `new` | medium | 4096 | 30600000 | 3.86 | 10.20 | 0.38x | yes | argument-free |
| `new` | large | 262144 | 54400000 | 3.50 | 9.13 | 0.38x | yes | argument-free |
| `new` | edge-empty | 0 | 32000000 | 3.41 | 9.33 | 0.37x | yes | argument-free |
| `from_list` | edge-empty | 0 | 300000 | 361.67 | 21.79 | 16.60x **over** | yes | - |
| `length` | edge-empty | 0 | 192000000 | 0.99 | 2.84 | 0.35x | yes | argument-free, barrier-dominated |
| `add` | edge-empty | 0 | 32000000 | 3.44 | 1.01 | 3.40x **over** | yes | barrier-dominated |
| `prefix_sum` | edge-empty | 0 | 20400000 | 5.98 | 1.05 | 5.71x **over** | yes | barrier-dominated |
| `range_sum` | edge-empty | 0 | 19200000 | 6.17 | 1.49 | 4.15x **over** | yes | barrier-dominated |

### `graph`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `add_vertex` | small | 32 | 1050000 | 145.24 | 17.63 | 8.24x **over** | yes | - |
| `add_vertex` | medium | 512 | 420000 | 248.81 | 29.07 | 8.56x **over** | yes | - |
| `add_vertex` | large | 4096 | 520000 | 325.00 | 40.73 | 7.98x **over** | yes | - |
| `remove_vertex` | small | 32 | 16384000 | 7.78 | 1.00 | 7.79x **over** | yes | barrier-dominated |
| `remove_vertex` | medium | 512 | - | FAILED | FAILED | - | - | sample 0: A-B = 39000000ns (bend) / 22619000ns (reference), below the 50000000ns / 100000ns minima |
| `remove_vertex` | large | 4096 | 400 | 296250.00 | 38505.00 | 7.69x **over** | yes | - |
| `add_edge` | small | 32 | 100000 | 1700.00 | 76.09 | 22.34x **over** | yes | - |
| `add_edge` | medium | 512 | 40000 | 5550.00 | 465.34 | 11.93x **over** | yes | - |
| `add_edge` | large | 4096 | 30000 | 5116.67 | 480.43 | 10.65x **over** | yes | - |
| `remove_edge` | small | 32 | 600000 | 319.17 | 42.89 | 7.44x **over** | yes | - |
| `remove_edge` | medium | 512 | 160000 | 496.88 | 71.70 | 6.93x **over** | yes | - |
| `remove_edge` | large | 4096 | 260000 | 703.85 | 104.82 | 6.71x **over** | yes | - |
| `has_vertex` | small | 32 | 1500000 | 119.00 | 17.39 | 6.84x **over** | yes | - |
| `has_vertex` | medium | 512 | 520000 | 214.42 | 32.78 | 6.54x **over** | yes | - |
| `has_vertex` | large | 4096 | 510000 | 450.00 | 59.80 | 7.53x **over** | yes | - |
| `has_edge` | small | 32 | 250000 | 460.00 | 58.10 | 7.92x **over** | yes | - |
| `has_edge` | medium | 512 | 160000 | 765.62 | 110.62 | 6.92x **over** | yes | - |
| `has_edge` | large | 4096 | 110000 | 1240.91 | 180.08 | 6.89x **over** | yes | - |
| `neighbors` | small | 32 | 350000 | 324.29 | 38.07 | 8.52x **over** | yes | - |
| `neighbors` | medium | 512 | 220000 | 479.55 | 63.22 | 7.59x **over** | yes | - |
| `neighbors` | large | 4096 | 150000 | 653.33 | 98.83 | 6.61x **over** | yes | - |
| `vertices` | small | 32 | 150000 | 1430.00 | 57.42 | 24.90x **over** | yes | argument-free |
| `vertices` | medium | 512 | 5000 | 20500.00 | 901.10 | 22.75x **over** | yes | argument-free |
| `vertices` | large | 4096 | 500 | 196000.00 | 7360.00 | 26.63x **over** | yes | argument-free |
| `edges` | small | 32 | 30000 | 3583.33 | 180.38 | 19.87x **over** | yes | argument-free |
| `edges` | medium | 512 | 1500 | 76333.33 | 3844.67 | 19.85x **over** | yes | argument-free |
| `edges` | large | 4096 | 300 | 826666.67 | 33120.00 | 24.96x **over** | yes | argument-free |
| `new` | small | 32 | 20400000 | 6.15 | 2.48 | 2.48x | yes | argument-free, barrier-dominated |
| `new` | medium | 512 | 19200000 | 6.67 | 2.73 | 2.45x | yes | argument-free, barrier-dominated |
| `new` | large | 4096 | 19200000 | 6.20 | 2.44 | 2.54x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 20400000 | 6.27 | 2.43 | 2.58x **over** | yes | argument-free, barrier-dominated |
| `add_vertex` | edge-empty | 0 | 3400000 | 35.59 | 1.60 | 22.18x **over** | yes | barrier-dominated |
| `remove_vertex` | edge-empty | 0 | 12800000 | 10.23 | 1.60 | 6.38x **over** | yes | barrier-dominated |
| `add_edge` | edge-empty | 0 | 10200000 | 19.46 | 1.68 | 11.58x **over** | yes | barrier-dominated |
| `remove_edge` | edge-empty | 0 | 6400000 | 19.45 | 1.76 | 11.07x **over** | yes | barrier-dominated |
| `has_vertex` | edge-empty | 0 | 12800000 | 10.27 | 1.75 | 5.87x **over** | yes | barrier-dominated |
| `has_edge` | edge-empty | 0 | 5100000 | 22.25 | 1.77 | 12.55x **over** | yes | barrier-dominated |
| `neighbors` | edge-empty | 0 | 12800000 | 15.04 | 1.83 | 8.21x **over** | yes | barrier-dominated |
| `vertices` | edge-empty | 0 | 19200000 | 9.19 | 4.61 | 1.99x | yes | argument-free |
| `edges` | edge-empty | 0 | 25600000 | 12.66 | 4.44 | 2.85x **over** | yes | argument-free |

### `prefix_trie`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `insert` | small | 64 | 250000 | 686.00 | 116.04 | 5.91x **over** | yes | - |
| `insert` | medium | 2048 | 300000 | 453.33 | 96.47 | 4.70x **over** | yes | - |
| `insert` | large | 32768 | - | FAILED | FAILED | - | - | sample 5: A-B = -106000000ns (bend) / 76471000ns (reference), below the 50000000ns / 100000ns minima |
| `lookup` | small | 64 | 500000 | 219.00 | 24.13 | 9.07x **over** | yes | - |
| `lookup` | medium | 2048 | 300000 | 308.33 | 44.95 | 6.86x **over** | yes | - |
| `lookup` | large | 32768 | 320000 | 496.88 | 85.70 | 5.80x **over** | yes | - |
| `remove` | small | 64 | 500000 | 230.00 | 24.51 | 9.38x **over** | yes | - |
| `remove` | medium | 2048 | 300000 | 328.33 | 46.80 | 7.02x **over** | yes | - |
| `remove` | large | 32768 | - | FAILED | FAILED | - | - | sample 0: A-B = -31000000ns (bend) / 58587000ns (reference), below the 50000000ns / 100000ns minima |
| `contains` | small | 64 | 500000 | 225.00 | 25.40 | 8.86x **over** | yes | - |
| `contains` | medium | 2048 | 600000 | 311.67 | 45.62 | 6.83x **over** | yes | - |
| `contains` | large | 32768 | 640000 | 523.44 | 84.71 | 6.18x **over** | yes | - |
| `prefix_entries` | small | 64 | 170000 | 1073.53 | 73.02 | 14.70x **over** | yes | - |
| `prefix_entries` | medium | 2048 | 3000 | 36333.33 | 1901.33 | 19.11x **over** | yes | - |
| `prefix_entries` | large | 32768 | 160 | 1000000.00 | 28062.50 | 35.63x **over** | yes | - |
| `longest_prefix` | small | 64 | 600000 | 189.17 | 26.58 | 7.12x **over** | yes | - |
| `longest_prefix` | medium | 2048 | 680000 | 255.88 | 48.04 | 5.33x **over** | yes | - |
| `longest_prefix` | large | 32768 | 640000 | 445.31 | 95.16 | 4.68x **over** | yes | - |
| `new` | small | 64 | 108800000 | 1.01 | 2.53 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | medium | 2048 | 166400000 | 1.02 | 2.53 | 0.40x | yes | argument-free, barrier-dominated |
| `new` | large | 32768 | 144000000 | 0.99 | 2.54 | 0.39x | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 108800000 | 1.01 | 2.53 | 0.40x | yes | argument-free, barrier-dominated |
| `insert` | edge-empty | 0 | 300000 | 1038.33 | 192.71 | 5.39x **over** | yes | - |
| `lookup` | edge-empty | 0 | 800000 | 137.50 | 1.26 | 109.34x **over** | yes | barrier-dominated |
| `remove` | edge-empty | 0 | 800000 | 136.88 | 1.27 | 107.62x **over** | yes | barrier-dominated |
| `contains` | edge-empty | 0 | 700000 | 142.14 | 1.28 | 110.93x **over** | yes | barrier-dominated |
| `prefix_entries` | edge-empty | 0 | 5100000 | 24.02 | 3.81 | 6.31x **over** | yes | - |
| `longest_prefix` | edge-empty | 0 | 700000 | 155.00 | 2.87 | 54.09x **over** | yes | barrier-dominated |

### `queue`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `enqueue` | small | 64 | 10400000 | 9.62 | 1.31 | 7.32x **over** | yes | barrier-dominated |
| `enqueue` | medium | 4096 | 12800000 | 9.30 | 1.32 | 7.02x **over** | yes | barrier-dominated |
| `enqueue` | large | 262144 | 10200000 | 8.43 | 1.21 | 6.95x **over** | yes | barrier-dominated |
| `peek` | small | 64 | 20400000 | 4.90 | 1.17 | 4.17x **over** | yes | argument-free, barrier-dominated |
| `peek` | medium | 4096 | 25500000 | 4.65 | 1.13 | 4.13x **over** | yes | argument-free, barrier-dominated |
| `peek` | large | 262144 | 22950000 | 4.88 | 1.16 | 4.22x **over** | yes | argument-free, barrier-dominated |
| `length` | small | 64 | 89600000 | 0.99 | 2.49 | 0.40x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 192000000 | 0.99 | 2.49 | 0.40x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 166400000 | 1.00 | 2.53 | 0.40x | yes | argument-free, barrier-dominated |
| `to_list` | small | 64 | 220000 | 915.91 | 125.15 | 7.32x **over** | yes | argument-free |
| `to_list` | medium | 4096 | 2000 | 82500.00 | 7777.00 | 10.61x **over** | yes | argument-free |
| `to_list` | large | 262144 | 50 | 5320000.00 | 479570.00 | 11.09x **over** | yes | argument-free |
| `dequeue` | small | 64 | 13369344 | 24.61 | 6.74 | 3.65x **over** | yes | - |
| `dequeue` | medium | 4096 | 5505024 | 35.88 | 6.21 | 5.78x **over** | yes | - |
| `dequeue` | large | 262144 | 5898240 | 30.77 | 5.40 | 5.69x **over** | yes | - |
| `new` | small | 64 | 128000000 | 1.34 | 3.34 | 0.40x | yes | argument-free |
| `new` | medium | 4096 | 89600000 | 1.50 | 3.42 | 0.44x | yes | argument-free |
| `new` | large | 262144 | 132600000 | 1.40 | 3.71 | 0.38x | yes | argument-free |
| `new` | edge-empty | 0 | 76800000 | 1.27 | 3.13 | 0.41x | yes | argument-free |
| `length` | edge-empty | 0 | 76800000 | 1.04 | 2.51 | 0.41x | yes | argument-free, barrier-dominated |
| `enqueue` | edge-empty | 0 | 13600000 | 8.24 | 1.15 | 7.18x **over** | yes | barrier-dominated |
| `dequeue` | edge-empty | 0 | 13600000 | 7.35 | 2.08 | 3.54x **over** | yes | barrier-dominated |
| `peek` | edge-empty | 0 | 20400000 | 7.35 | 2.01 | 3.66x **over** | yes | argument-free, barrier-dominated |
| `to_list` | edge-empty | 0 | 25600000 | 6.00 | 1.20 | 5.01x **over** | yes | argument-free, barrier-dominated |

### `segment_tree`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `range_add` | small | 64 | 1050000 | 99.05 | 26.59 | 3.72x **over** | yes | - |
| `range_add` | medium | 4096 | 680000 | 238.97 | 50.88 | 4.70x **over** | yes | - |
| `range_add` | large | 262144 | 1280000 | 107.42 | 20.20 | 5.32x **over** | yes | - |
| `get` | small | 64 | 2550000 | 52.94 | 3.25 | 16.28x **over** | yes | - |
| `get` | medium | 4096 | 1040000 | 138.94 | 6.00 | 23.17x **over** | yes | - |
| `get` | large | 262144 | 640000 | 342.19 | 9.53 | 35.91x **over** | yes | - |
| `range_query` | small | 64 | 2550000 | 62.75 | 20.25 | 3.10x **over** | yes | - |
| `range_query` | medium | 4096 | 680000 | 154.41 | 37.63 | 4.10x **over** | yes | - |
| `range_query` | large | 262144 | 2560000 | 73.83 | 12.54 | 5.89x **over** | yes | - |
| `length` | small | 64 | 115200000 | 1.00 | 2.85 | 0.35x | yes | argument-free, barrier-dominated |
| `length` | medium | 4096 | 192000000 | 1.00 | 2.78 | 0.36x | yes | argument-free, barrier-dominated |
| `length` | large | 262144 | 115200000 | 0.96 | 2.75 | 0.35x | yes | argument-free, barrier-dominated |
| `set` | small | 64 | 1300000 | 88.08 | 8.25 | 10.68x **over** | yes | - |
| `set` | medium | 4096 | 520000 | 230.77 | 17.77 | 12.99x **over** | yes | - |
| `set` | large | 262144 | 640000 | 509.38 | 44.10 | 11.55x **over** | yes | - |
| `from_list` | small | 64 | 16000000 | 458.59 | 52.48 | 8.74x **over** | yes | - |
| `from_list` | medium | 4096 | 250000 | 444.00 | 51.69 | 8.59x **over** | yes | - |
| `from_list` | large | 262144 | 300000 | 400.00 | 50.60 | 7.91x **over** | yes | - |
| `new` | small | 64 | 38400000 | 3.50 | 9.42 | 0.37x | yes | argument-free |
| `new` | medium | 4096 | 38400000 | 3.50 | 9.43 | 0.37x | yes | argument-free |
| `new` | large | 262144 | 57600000 | 3.47 | 9.64 | 0.36x | yes | argument-free |
| `new` | edge-empty | 0 | 32000000 | 3.50 | 9.27 | 0.38x | yes | argument-free |
| `from_list` | edge-empty | 0 | 300000 | 410.00 | 51.95 | 7.89x **over** | yes | - |
| `length` | edge-empty | 0 | 108800000 | 1.02 | 2.90 | 0.35x | yes | argument-free, barrier-dominated |
| `get` | edge-empty | 0 | 32000000 | 3.36 | 1.07 | 3.13x **over** | yes | barrier-dominated |
| `set` | edge-empty | 0 | 51200000 | 3.47 | 1.02 | 3.40x **over** | yes | barrier-dominated |
| `range_query` | edge-empty | 0 | 25600000 | 6.33 | 1.50 | 4.22x **over** | yes | barrier-dominated |
| `range_add` | edge-empty | 0 | 19200000 | 6.74 | 2.58 | 2.62x **over** | yes | barrier-dominated |

### `union_find`

| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |
|---|---|---|---|---|---|---|---|---|
| `find` | small | 64 | 76800000 | 1.45 | 1.27 | 1.14x | yes | barrier-dominated |
| `find` | medium | 4096 | 83200000 | 1.31 | 1.15 | 1.14x | yes | barrier-dominated |
| `find` | large | 65536 | 99840000 | 1.37 | 1.16 | 1.19x | yes | barrier-dominated |
| `union` | small | 64 | 25600000 | 4.10 | 1.53 | 2.67x **over** | yes | barrier-dominated |
| `union` | medium | 4096 | 28800000 | 3.70 | 1.31 | 2.82x **over** | yes | barrier-dominated |
| `union` | large | 65536 | - | FAILED | FAILED | - | - | sample 2: A-B = -97000000ns (bend) / 3897000ns (reference), below the 50000000ns / 100000ns minima |
| `connected` | small | 64 | 51200000 | 2.25 | 1.58 | 1.42x | yes | barrier-dominated |
| `connected` | medium | 4096 | 67200000 | 2.02 | 1.36 | 1.49x | yes | barrier-dominated |
| `connected` | large | 65536 | 87040000 | 2.15 | 1.48 | 1.45x | yes | barrier-dominated |
| `component_size` | small | 64 | 76800000 | 1.52 | 1.29 | 1.18x | yes | barrier-dominated |
| `component_size` | medium | 4096 | 83200000 | 1.41 | 1.18 | 1.19x | yes | barrier-dominated |
| `component_size` | large | 65536 | 87040000 | 1.59 | 1.28 | 1.24x | yes | barrier-dominated |
| `component_count` | small | 64 | 102400000 | 1.00 | 2.73 | 0.36x | yes | argument-free, barrier-dominated |
| `component_count` | medium | 4096 | 108800000 | 1.00 | 2.73 | 0.36x | yes | argument-free, barrier-dominated |
| `component_count` | large | 65536 | 108800000 | 1.01 | 2.74 | 0.37x | yes | argument-free, barrier-dominated |
| `new` | small | 64 | 3400000 | 33.82 | 1.80 | 18.80x **over** | yes | argument-free, barrier-dominated |
| `new` | medium | 4096 | 3400000 | 34.12 | 1.81 | 18.89x **over** | yes | argument-free, barrier-dominated |
| `new` | large | 65536 | 3400000 | 34.41 | 1.80 | 19.12x **over** | yes | argument-free, barrier-dominated |
| `new` | edge-empty | 0 | 5200000 | 34.04 | 1.81 | 18.83x **over** | yes | argument-free, barrier-dominated |
| `find` | edge-empty | 0 | 166400000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `union` | edge-empty | 0 | 32000000 | 3.39 | 1.11 | 3.05x **over** | yes | barrier-dominated |
| `connected` | edge-empty | 0 | 70400000 | 1.56 | 1.10 | 1.41x | yes | barrier-dominated |
| `component_size` | edge-empty | 0 | 166400000 | 1.11 | 1.01 | 1.10x | yes | barrier-dominated |
| `component_count` | edge-empty | 0 | 134400000 | 0.99 | 2.73 | 0.36x | yes | argument-free, barrier-dominated |

## Individual samples

Every sample of every measured row, nanoseconds per operation, in the
order taken (Bend and reference alternate within a row):

```
dynamic_array.push                       small        bend 23.46 25.38 25.96 21.54 23.08 19.62
                                                      ref  3.79 3.83 3.54 3.62 2.95 3.05
dynamic_array.push                       medium       bend 18.53 20.39 20.00 19.90 16.47 18.92
                                                      ref  3.14 3.46 3.27 3.36 3.14 3.23
dynamic_array.get                        small        bend 2.11 2.19 2.40 2.15 2.23 1.93
                                                      ref  1.82 1.84 1.78 2.14 1.83 1.77
dynamic_array.get                        medium       bend 2.00 1.92 2.12 1.86 1.84 1.78
                                                      ref  1.68 1.62 1.50 1.62 1.56 1.76
dynamic_array.get                        large        bend 2.50 2.10 2.17 2.17 2.37 2.15
                                                      ref  1.72 1.84 1.62 1.64 1.60 1.54
dynamic_array.set                        small        bend 1.81 1.91 1.89 1.81 2.06 1.70
                                                      ref  1.79 1.83 1.72 1.83 1.74 1.92
dynamic_array.set                        medium       bend 1.78 1.52 1.59 1.56 1.52 1.70
                                                      ref  1.44 1.63 1.58 1.55 1.51 1.51
dynamic_array.set                        large        bend 1.83 1.86 1.98 1.69 1.71 1.70
                                                      ref  1.75 1.81 1.68 1.69 1.53 1.72
dynamic_array.length                     small        bend 1.24 1.30 1.37 1.29 1.22 1.24
                                                      ref  3.30 3.68 3.70 3.34 3.40 3.33
dynamic_array.length                     medium       bend 1.22 1.20 1.30 1.20 1.26 1.26
                                                      ref  3.47 3.81 3.75 3.79 3.49 3.48
dynamic_array.length                     large        bend 1.42 1.18 1.21 1.21 1.32 1.35
                                                      ref  3.62 3.39 3.46 3.86 3.79 3.62
dynamic_array.capacity                   small        bend 6.37 6.57 6.37 6.76 6.47 6.52
                                                      ref  3.74 3.48 3.67 3.42 3.50 3.48
dynamic_array.capacity                   medium       bend 10.26 10.20 10.26 10.92 9.02 10.20
                                                      ref  3.90 3.22 3.88 3.30 3.64 3.24
dynamic_array.capacity                   large        bend 13.33 13.85 12.50 12.50 12.60 13.02
                                                      ref  3.51 3.49 3.66 3.49 3.51 3.49
dynamic_array.reserve                    small        bend 22.50 21.62 22.50 23.09 22.50 20.59
                                                      ref  1.51 1.52 1.71 1.48 1.66 1.67
dynamic_array.reserve                    medium       bend 26.03 22.79 24.26 23.53 23.82 25.29
                                                      ref  1.49 1.67 1.69 1.63 1.71 1.66
dynamic_array.reserve                    large        bend 32.55 21.96 37.65 34.12 33.73 30.98
                                                      ref  1.77 1.21 3.12 1.66 1.91 2.08
dynamic_array.to_list                    small        bend 1190.00 1140.00 1130.00 1130.00 1140.00 1190.00
                                                      ref  103.58 103.72 104.50 104.43 104.30 103.71
dynamic_array.to_list                    medium       bend 89500.00 91500.00 80000.00 99000.00 94000.00 96000.00
                                                      ref  6326.50 5794.00 6568.50 6332.50 5753.00 5774.00
dynamic_array.to_list                    large        bend 5800000.00 6380000.00 5860000.00 7660000.00 7160000.00 6560000.00
                                                      ref  474660.00 479000.00 510280.00 548360.00 460340.00 561820.00
dynamic_array.clear                      small        bend 68.24 69.41 63.53 64.12 64.12 63.53
                                                      ref  8.71 7.95 7.95 7.95 8.64 7.96
dynamic_array.clear                      medium       bend 3800.00 3675.00 3800.00 3850.00 3725.00 3875.00
                                                      ref  955.38 809.85 642.12 278.07 400.50 527.48
dynamic_array.clear                      large        bend 254000.00 252000.00 248000.00 276000.00 250000.00 232000.00
                                                      ref  13476.00 12476.00 14934.00 12540.00 13076.00 12616.00
dynamic_array.new                        small        bend 4.53 5.20 4.49 4.80 4.77 5.39
                                                      ref  3.38 3.23 3.41 3.35 3.67 3.49
dynamic_array.new                        medium       bend 4.88 5.12 4.84 5.08 4.96 5.16
                                                      ref  3.60 3.22 3.69 3.41 3.56 3.07
dynamic_array.new                        large        bend 4.58 5.10 4.49 5.05 4.84 5.49
                                                      ref  3.36 3.17 3.52 3.25 3.59 3.26
dynamic_array.new                        edge-empty   bend 4.65 5.04 4.14 5.00 4.88 5.00
                                                      ref  3.52 3.00 4.03 3.17 3.33 3.13
dynamic_array.length                     edge-empty   bend 1.32 1.13 1.18 1.17 1.16 1.33
                                                      ref  3.90 3.32 3.31 3.45 3.63 3.30
dynamic_array.capacity                   edge-empty   bend 3.98 4.69 4.38 4.65 4.26 4.41
                                                      ref  3.56 3.20 3.23 3.12 3.24 3.10
dynamic_array.get                        edge-empty   bend 1.59 1.52 1.47 1.95 1.72 1.88
                                                      ref  1.25 1.42 1.56 1.81 1.55 1.55
dynamic_array.set                        edge-empty   bend 1.61 1.56 1.52 1.45 1.50 1.44
                                                      ref  1.42 1.42 1.39 1.32 1.28 1.35
dynamic_array.push                       edge-empty   bend 18.82 18.97 18.97 19.26 19.26 19.41
                                                      ref  2.98 2.97 2.79 3.32 3.11 3.13
dynamic_array.pop                        edge-empty   bend 1.33 1.28 1.33 1.16 1.28 1.17
                                                      ref  1.28 1.30 1.27 1.28 1.15 1.32
dynamic_array.reserve                    edge-empty   bend 17.50 19.04 20.19 20.19 18.37 17.69
                                                      ref  1.57 1.57 1.45 1.57 1.57 1.57
dynamic_array.clear                      edge-empty   bend 4.14 4.73 5.31 4.69 3.95 4.69
                                                      ref  2.52 2.30 2.68 2.38 2.47 2.39
dynamic_array.to_list                    edge-empty   bend 7.89 9.14 8.67 8.36 9.14 9.38
                                                      ref  2.61 2.39 2.27 2.19 2.28 2.42
deque.push_front                         small        bend 12.60 11.63 13.08 12.21 11.06 11.15
                                                      ref  3.58 4.00 3.28 3.39 3.41 3.38
deque.push_front                         medium       bend 11.88 11.09 11.41 11.80 11.33 11.64
                                                      ref  3.43 3.50 3.44 3.42 3.43 3.40
deque.push_back                          small        bend 12.60 12.60 12.69 12.40 11.44 11.44
                                                      ref  1.56 1.72 1.76 1.68 1.62 1.77
deque.push_back                          medium       bend 10.98 11.76 11.67 10.69 12.84 15.20
                                                      ref  1.51 1.73 1.55 1.67 1.45 1.84
deque.peek_front                         small        bend 5.98 6.02 5.86 6.05 5.90 5.59
                                                      ref  1.40 1.52 1.40 1.60 1.56 1.65
deque.peek_front                         medium       bend 5.73 5.05 5.47 5.57 5.36 5.36
                                                      ref  1.58 1.43 1.43 1.44 1.42 1.51
deque.peek_front                         large        bend 5.78 5.52 6.09 6.20 5.42 6.30
                                                      ref  1.29 1.42 1.72 1.41 1.68 1.55
deque.peek_back                          small        bend 6.03 6.18 5.54 5.88 5.93 6.03
                                                      ref  1.43 1.57 1.56 1.56 1.57 1.49
deque.peek_back                          medium       bend 6.20 5.83 5.78 5.83 5.05 5.47
                                                      ref  1.37 1.66 1.42 1.46 1.42 1.64
deque.peek_back                          large        bend 5.59 5.54 5.39 5.15 5.93 6.03
                                                      ref  1.45 1.41 1.51 1.54 1.44 1.43
deque.length                             small        bend 1.22 1.16 1.35 1.22 1.15 1.20
                                                      ref  3.00 3.15 3.19 3.05 3.40 2.98
deque.length                             medium       bend 1.22 1.23 1.26 1.14 1.33 1.35
                                                      ref  2.89 3.22 2.95 3.70 3.11 3.60
deque.length                             large        bend 1.34 1.15 1.22 1.12 1.20 1.21
                                                      ref  3.17 2.96 2.86 2.99 3.05 3.25
deque.to_list                            small        bend 928.57 878.57 892.86 1007.14 978.57 707.14
                                                      ref  112.66 112.66 113.46 113.31 114.29 107.06
deque.to_list                            medium       bend 65000.00 71000.00 65500.00 73500.00 67000.00 76000.00
                                                      ref  7808.50 6918.50 7093.50 6968.00 6972.50 6873.00
deque.to_list                            large        bend 4360000.00 4960000.00 4320000.00 4880000.00 4680000.00 4700000.00
                                                      ref  454160.00 388420.00 425040.00 420960.00 414320.00 391520.00
deque.pop_front                          small        bend 20.64 24.08 21.39 19.75 21.69 22.89
                                                      ref  5.95 5.82 6.86 6.00 6.42 6.38
deque.pop_front                          medium       bend 27.43 37.42 19.98 33.61 21.80 41.05
                                                      ref  4.54 5.29 4.66 6.06 5.48 5.96
deque.pop_front                          large        bend 23.61 29.79 19.62 23.98 29.06 32.70
                                                      ref  4.49 4.69 5.35 4.81 4.79 4.97
deque.new                                small        bend 1.23 1.16 1.19 1.19 1.16 1.29
                                                      ref  3.07 3.01 2.90 2.99 2.97 3.30
deque.new                                medium       bend 1.21 1.22 1.22 1.22 1.28 1.26
                                                      ref  3.05 2.94 3.03 3.04 2.92 3.18
deque.new                                large        bend 1.28 1.21 1.22 1.22 1.28 1.24
                                                      ref  3.05 3.11 3.05 3.24 3.24 3.39
deque.new                                edge-empty   bend 1.21 1.13 1.25 1.24 1.24 1.33
                                                      ref  3.03 3.00 3.05 3.32 3.14 3.21
deque.length                             edge-empty   bend 1.23 1.22 1.25 1.15 1.24 1.67
                                                      ref  3.09 3.06 2.98 3.00 2.66 3.26
deque.push_front                         edge-empty   bend 11.03 12.57 12.79 11.54 11.25 11.69
                                                      ref  3.93 3.32 3.40 3.40 3.32 3.22
deque.push_back                          edge-empty   bend 11.83 12.21 11.73 12.40 12.21 12.60
                                                      ref  1.51 1.82 1.73 1.69 1.74 1.70
deque.pop_front                          edge-empty   bend 10.00 10.00 9.41 9.90 9.80 9.51
                                                      ref  2.68 2.32 2.68 2.43 2.82 2.45
deque.pop_back                           edge-empty   bend 9.14 9.53 9.38 9.84 9.30 9.61
                                                      ref  2.47 2.51 2.48 2.44 2.55 2.34
deque.peek_front                         edge-empty   bend 10.00 11.18 10.20 10.39 10.39 10.49
                                                      ref  2.57 2.67 2.68 2.68 2.67 2.68
deque.peek_back                          edge-empty   bend 10.29 9.63 10.00 10.07 8.90 9.49
                                                      ref  2.67 2.68 2.32 2.60 2.40 2.66
deque.to_list                            edge-empty   bend 8.05 8.67 7.97 8.05 8.05 8.12
                                                      ref  1.44 1.58 1.49 1.56 1.55 1.54
queue.enqueue                            small        bend 10.58 9.42 10.10 9.62 9.62 9.52
                                                      ref  1.39 1.30 1.33 1.28 1.33 1.30
queue.enqueue                            medium       bend 9.61 9.30 9.38 9.30 9.30 8.83
                                                      ref  1.17 1.36 1.34 1.31 1.33 1.30
queue.enqueue                            large        bend 6.47 10.20 6.86 6.27 10.00 16.96
                                                      ref  1.67 1.18 1.49 1.10 1.20 1.22
queue.peek                               small        bend 5.29 4.90 4.90 4.90 5.00 4.66
                                                      ref  1.18 1.17 1.17 1.18 1.13 1.13
queue.peek                               medium       bend 4.75 4.71 4.59 4.71 4.47 4.59
                                                      ref  1.13 1.13 1.13 1.13 1.12 1.13
queue.peek                               large        bend 4.79 4.66 4.71 5.01 4.97 5.01
                                                      ref  1.14 1.13 1.15 1.18 1.19 1.16
queue.length                             small        bend 1.00 0.99 0.99 0.98 0.99 1.02
                                                      ref  2.49 2.50 2.49 2.48 2.50 2.51
queue.length                             medium       bend 0.99 1.01 0.98 0.99 0.99 0.99
                                                      ref  2.48 2.49 2.48 2.50 2.48 2.49
queue.length                             large        bend 1.00 0.99 1.01 1.02 1.03 1.00
                                                      ref  2.48 2.52 2.55 2.49 2.56 2.74
queue.to_list                            small        bend 604.55 790.91 868.18 963.64 1072.73 1022.73
                                                      ref  81.03 104.40 122.00 129.29 141.15 128.31
queue.to_list                            medium       bend 80500.00 88000.00 84500.00 89000.00 75000.00 79500.00
                                                      ref  7840.50 8546.50 7704.00 7586.00 9163.00 7713.50
queue.to_list                            large        bend 4940000.00 5300000.00 5220000.00 5480000.00 5340000.00 6440000.00
                                                      ref  478460.00 480680.00 504540.00 467120.00 467700.00 482440.00
queue.dequeue                            small        bend 24.98 24.23 19.97 26.85 22.59 25.36
                                                      ref  7.08 7.37 10.30 6.36 6.39 6.22
queue.dequeue                            medium       bend 23.43 76.48 36.69 35.06 33.61 39.78
                                                      ref  6.18 6.23 7.07 6.79 6.11 5.57
queue.dequeue                            large        bend 8.82 34.76 30.35 31.20 32.38 28.48
                                                      ref  11.43 8.18 5.49 5.32 4.57 4.67
queue.new                                small        bend 1.34 1.71 1.95 1.34 1.31 1.23
                                                      ref  2.71 4.63 4.35 3.23 3.23 3.44
queue.new                                medium       bend 1.24 2.03 1.72 1.53 1.46 1.29
                                                      ref  3.25 4.45 4.32 3.35 3.48 3.27
queue.new                                large        bend 1.33 1.29 2.22 1.69 1.48 1.29
                                                      ref  3.43 5.50 4.26 3.27 3.26 4.00
queue.new                                edge-empty   bend 1.30 1.28 1.30 1.18 1.26 1.20
                                                      ref  3.27 3.23 3.12 3.05 3.14 3.07
queue.length                             edge-empty   bend 1.43 1.15 1.07 1.00 0.96 0.99
                                                      ref  3.77 2.51 2.52 2.51 2.50 2.50
queue.enqueue                            edge-empty   bend 8.09 8.16 7.94 8.31 8.38 10.15
                                                      ref  1.12 1.11 1.15 1.15 1.25 1.44
queue.dequeue                            edge-empty   bend 7.65 6.99 7.65 7.50 7.21 7.21
                                                      ref  2.13 2.19 2.03 2.01 2.13 2.00
queue.peek                               edge-empty   bend 7.35 7.40 7.35 7.11 6.96 7.35
                                                      ref  2.02 2.02 2.05 2.00 2.00 1.96
queue.to_list                            edge-empty   bend 5.82 6.13 5.70 6.09 5.90 6.29
                                                      ref  1.17 1.26 1.25 1.16 1.22 1.12
doubly_linked_list.push_front            small        bend 4250.00 4230.00 4210.00 4240.00 4260.00 4260.00
                                                      ref  233.75 253.03 223.09 258.81 234.20 254.40
doubly_linked_list.push_front            medium       bend 3980.00 4020.00 4020.00 3980.00 3960.00 3980.00
                                                      ref  183.50 209.46 190.74 210.36 186.66 204.92
doubly_linked_list.push_front            large        bend 3875.00 3900.00 3725.00 4475.00 3950.00 4125.00
                                                      ref  190.57 192.90 189.93 210.70 176.72 190.30
doubly_linked_list.push_back             small        bend 4430.00 4500.00 4370.00 4350.00 4230.00 4760.00
                                                      ref  288.22 259.37 234.77 254.38 229.30 261.53
doubly_linked_list.push_back             medium       bend 4320.00 4160.00 4120.00 4040.00 4020.00 4180.00
                                                      ref  195.02 212.58 214.96 209.52 192.56 227.58
doubly_linked_list.push_back             large        bend 3825.00 8925.00 7875.00 5225.00 8100.00 4775.00
                                                      ref  197.18 350.48 319.20 247.03 186.12 230.00
doubly_linked_list.insert_before         small        bend 6200.00 6100.00 5910.00 6360.00 6100.00 6410.00
                                                      ref  360.91 394.26 365.98 380.21 364.94 394.30
doubly_linked_list.insert_before         medium       bend 5780.00 6040.00 5760.00 5820.00 5620.00 6000.00
                                                      ref  371.98 371.92 353.64 358.78 366.64 373.34
doubly_linked_list.insert_before         large        bend 4850.00 6250.00 4500.00 6150.00 5350.00 5850.00
                                                      ref  452.05 494.05 450.90 502.05 504.70 500.60
doubly_linked_list.insert_after          small        bend 6200.00 6190.00 6240.00 6310.00 6140.00 6510.00
                                                      ref  485.11 509.87 448.37 435.36 408.97 438.49
doubly_linked_list.insert_after          medium       bend 5760.00 5740.00 5600.00 6040.00 5620.00 6700.00
                                                      ref  403.72 392.86 398.36 421.18 390.84 450.28
doubly_linked_list.insert_after          large        bend 5600.00 6600.00 5250.00 6150.00 5300.00 12050.00
                                                      ref  470.80 494.70 455.60 483.50 459.95 793.60
doubly_linked_list.get                   small        bend 252.50 257.50 232.50 237.50 240.00 270.00
                                                      ref  32.39 33.26 32.42 31.61 32.05 35.07
doubly_linked_list.get                   medium       bend 427.50 445.00 450.00 440.00 447.50 435.00
                                                      ref  63.13 61.42 64.56 60.95 62.92 61.80
doubly_linked_list.get                   large        bend 557.14 985.71 864.29 878.57 1107.14 557.14
                                                      ref  173.68 193.12 146.24 177.46 169.31 197.81
doubly_linked_list.set                   small        bend 845.00 830.00 875.00 845.00 840.00 825.00
                                                      ref  32.10 31.25 32.55 31.24 32.90 31.76
doubly_linked_list.set                   medium       bend 1630.00 1640.00 1680.00 1630.00 1630.00 1640.00
                                                      ref  63.78 61.80 63.55 61.29 64.19 62.53
doubly_linked_list.set                   large        bend 1900.00 2300.00 2416.67 2616.67 2383.33 2616.67
                                                      ref  167.42 199.77 192.13 177.03 169.97 155.65
doubly_linked_list.next                  small        bend 220.00 232.00 228.00 220.00 230.00 222.00
                                                      ref  32.93 32.51 34.08 32.15 33.75 32.11
doubly_linked_list.next                  medium       bend 452.00 436.00 424.00 424.00 428.00 456.00
                                                      ref  63.28 60.64 65.97 62.88 63.23 62.23
doubly_linked_list.next                  large        bend 714.29 703.57 732.14 682.14 703.57 717.86
                                                      ref  170.75 227.06 183.22 176.85 216.63 172.88
doubly_linked_list.prev                  small        bend 226.00 210.00 222.00 222.00 224.00 222.00
                                                      ref  33.67 27.66 32.72 31.74 32.42 31.86
doubly_linked_list.prev                  medium       bend 596.00 428.00 420.00 476.00 416.00 460.00
                                                      ref  63.72 61.92 64.35 62.17 64.42 60.70
doubly_linked_list.prev                  large        bend 662.50 706.25 706.25 712.50 706.25 700.00
                                                      ref  154.41 173.97 170.85 161.18 167.26 175.74
doubly_linked_list.length                small        bend 6.18 6.27 5.49 5.49 5.49 5.49
                                                      ref  4.39 3.65 3.80 3.82 3.82 3.83
doubly_linked_list.length                medium       bend 5.05 8.23 6.38 5.62 5.52 6.15
                                                      ref  3.99 3.83 4.14 3.39 4.05 3.98
doubly_linked_list.length                large        bend 5.99 5.95 4.80 6.06 5.06 6.21
                                                      ref  3.82 3.55 4.00 3.48 4.34 3.65
doubly_linked_list.to_list               small        bend 14600.00 14900.00 14400.00 14300.00 14800.00 15000.00
                                                      ref  298.10 283.90 273.50 233.70 311.70 256.60
doubly_linked_list.to_list               medium       bend 873333.33 826666.67 870000.00 856666.67 876666.67 833333.33
                                                      ref  26563.33 23880.00 25996.67 24090.00 29873.33 28783.33
doubly_linked_list.to_list               large        bend 20550000.00 19150000.00 17900000.00 19550000.00 15900000.00 22150000.00
                                                      ref  1351700.00 1359950.00 1365150.00 1378650.00 1875250.00 1220500.00
doubly_linked_list.remove                small        bend 1259.00 1034.01 1153.68 1302.08 1957.91 1148.90
                                                      ref  52.88 50.28 55.57 55.38 53.49 48.95
doubly_linked_list.remove                medium       bend 3834.44 2556.30 2642.46 2326.52 2269.07 1910.04
                                                      ref  173.89 106.76 143.05 107.55 159.05 102.57
doubly_linked_list.remove                large        bend 3173.83 3814.70 3265.38 3845.21 3112.79 3540.04
                                                      ref  384.74 342.41 314.97 336.91 298.25 269.29
doubly_linked_list.new                   small        bend 1.41 1.55 1.66 1.65 1.69 1.38
                                                      ref  3.12 5.30 5.25 3.97 3.91 3.49
doubly_linked_list.new                   medium       bend 1.31 1.39 1.38 1.51 1.39 1.67
                                                      ref  3.37 3.46 3.48 3.53 3.15 3.82
doubly_linked_list.new                   edge-empty   bend 1.39 1.28 1.39 1.41 1.41 1.33
                                                      ref  3.48 3.33 3.43 3.47 3.49 4.71
doubly_linked_list.length                edge-empty   bend 1.44 1.41 1.40 1.44 1.46 1.45
                                                      ref  3.49 3.46 3.48 3.49 3.57 3.36
doubly_linked_list.push_front            edge-empty   bend 6460.00 6720.00 6580.00 6340.00 6540.00 6520.00
                                                      ref  359.98 395.55 358.79 382.53 334.44 364.10
doubly_linked_list.push_back             edge-empty   bend 6380.00 5850.00 6550.00 7030.00 7000.00 6770.00
                                                      ref  514.11 401.28 405.39 357.30 369.79 392.00
doubly_linked_list.insert_before         edge-empty   bend 15.94 17.50 16.88 16.88 16.88 14.84
                                                      ref  1.93 1.92 1.92 1.91 1.94 1.70
doubly_linked_list.insert_after          edge-empty   bend 14.41 15.29 15.00 15.78 15.39 19.22
                                                      ref  1.71 1.71 1.71 1.71 1.93 1.93
doubly_linked_list.remove                edge-empty   bend 15.78 16.88 16.09 17.19 14.84 13.44
                                                      ref  1.99 2.15 1.92 1.92 2.21 1.71
doubly_linked_list.get                   edge-empty   bend 16.57 14.02 13.92 13.24 14.31 12.75
                                                      ref  1.94 1.66 1.73 1.73 1.99 1.72
doubly_linked_list.set                   edge-empty   bend 17.06 13.82 14.51 13.63 13.63 13.82
                                                      ref  1.85 1.71 1.72 1.72 1.71 1.71
doubly_linked_list.next                  edge-empty   bend 6.08 6.72 6.32 6.67 6.47 6.91
                                                      ref  1.77 1.72 1.72 1.70 1.72 1.72
doubly_linked_list.prev                  edge-empty   bend 6.03 6.52 6.52 6.52 6.42 6.81
                                                      ref  1.71 1.71 1.71 1.71 1.71 1.72
doubly_linked_list.to_list               edge-empty   bend 8.05 8.44 8.44 10.16 7.97 8.91
                                                      ref  5.18 5.17 6.11 5.08 5.59 4.96
binary_heap.push                         small        bend 428.59 478.44 373.44 485.00 608.75 560.78
                                                      ref  89.59 96.21 93.06 90.50 88.64 84.83
binary_heap.push                         medium       bend 392.55 378.04 396.08 383.92 401.96 397.65
                                                      ref  59.55 58.57 61.56 56.28 63.40 54.91
binary_heap.peek                         small        bend 4.06 3.98 3.88 3.59 4.01 3.88
                                                      ref  1.56 1.30 1.43 1.62 1.55 1.39
binary_heap.peek                         medium       bend 3.59 4.44 4.28 5.09 4.34 4.34
                                                      ref  1.29 1.75 1.84 1.69 1.72 1.55
binary_heap.peek                         large        bend 4.55 3.50 3.31 3.88 3.40 3.82
                                                      ref  1.90 1.39 1.42 1.46 1.47 1.45
binary_heap.length                       small        bend 1.22 1.26 1.28 1.17 1.70 1.43
                                                      ref  3.60 3.57 3.58 4.29 4.29 3.45
binary_heap.length                       medium       bend 1.35 1.32 1.30 1.24 1.80 1.30
                                                      ref  4.18 3.73 3.64 5.12 4.90 3.79
binary_heap.length                       large        bend 1.14 1.79 1.06 1.25 1.04 1.09
                                                      ref  3.99 3.08 3.54 3.43 4.88 3.45
binary_heap.from_list                    small        bend 280.00 287.50 262.50 300.00 265.00 270.00
                                                      ref  60.94 40.02 58.66 39.47 63.07 34.38
binary_heap.from_list                    medium       bend 288.57 285.71 282.86 294.29 287.14 285.71
                                                      ref  56.08 34.33 59.49 34.33 57.65 35.70
binary_heap.from_list                    large        bend 269.53 283.59 287.50 285.94 264.84 275.78
                                                      ref  53.31 37.59 52.48 37.07 46.31 39.59
binary_heap.to_sorted_list               small        bend 17375.00 14750.00 17500.00 18750.00 18875.00 17500.00
                                                      ref  937.00 1003.88 1416.88 1252.00 1325.12 1185.12
binary_heap.to_sorted_list               medium       bend 2740000.00 2800000.00 2790000.00 2790000.00 2660000.00 2610000.00
                                                      ref  287700.00 260950.00 273920.00 295600.00 316460.00 291450.00
binary_heap.to_sorted_list               large        bend 160000000.00 165200000.00 158600000.00 206200000.00 130200000.00 169400000.00
                                                      ref  33679000.00 38219200.00 39750800.00 37653000.00 47532800.00 36333800.00
binary_heap.pop                          small        bend 360.11 250.24 196.84 192.26 157.17 193.79
                                                      ref  27.93 25.17 26.18 24.78 27.87 32.39
binary_heap.pop                          large        bend 923.16 2578.74 2487.18 816.35 1098.63 564.58
                                                      ref  180.95 199.13 256.74 126.86 236.10 27.68
binary_heap.new                          small        bend 1.15 1.11 1.22 1.22 1.18 1.18
                                                      ref  2.96 3.01 2.99 2.91 2.86 2.94
binary_heap.new                          medium       bend 1.18 1.23 1.58 1.40 1.33 1.16
                                                      ref  2.91 4.37 2.90 3.66 2.95 2.93
binary_heap.new                          large        bend 1.10 1.14 1.01 1.14 1.12 0.96
                                                      ref  3.17 2.98 3.27 3.00 2.30 2.91
binary_heap.new                          edge-empty   bend 1.23 1.24 1.15 1.21 1.23 1.21
                                                      ref  3.02 3.03 3.03 3.19 3.04 3.00
binary_heap.length                       edge-empty   bend 1.06 1.19 1.24 1.20 1.25 1.25
                                                      ref  5.04 3.39 3.49 3.50 3.43 5.15
binary_heap.push                         edge-empty   bend 405.00 402.06 520.00 406.18 128.53 376.47
                                                      ref  67.37 78.11 69.39 66.88 79.57 70.85
binary_heap.peek                         edge-empty   bend 3.69 3.31 3.81 3.53 3.47 3.66
                                                      ref  1.20 1.31 1.30 1.31 1.31 1.30
binary_heap.pop                          edge-empty   bend 4.45 4.53 4.22 4.22 4.26 3.91
                                                      ref  1.30 1.30 1.33 1.39 1.30 1.30
binary_heap.from_list                    edge-empty   bend 277.50 297.50 275.00 290.00 282.50 285.00
                                                      ref  68.84 36.45 58.33 45.45 54.34 41.34
binary_heap.to_sorted_list               edge-empty   bend 4.95 5.29 6.03 7.30 7.65 5.25
                                                      ref  5.08 4.76 4.84 6.34 6.49 5.01
balanced_search_tree.insert              small        bend 460.00 503.33 453.33 503.33 433.33 483.33
                                                      ref  36.68 38.81 42.95 33.46 40.54 38.69
balanced_search_tree.insert              medium       bend 1120.00 1240.00 1100.00 1150.00 1230.00 1220.00
                                                      ref  133.72 135.23 140.77 133.48 133.12 123.98
balanced_search_tree.insert              large        bend 1900.00 5550.00 2650.00 2583.33 1850.00 1266.67
                                                      ref  340.88 154.80 276.88 184.58 463.45 206.53
balanced_search_tree.remove              small        bend 6.67 8.28 7.14 8.39 7.50 7.97
                                                      ref  1.53 1.28 1.43 1.39 1.41 1.40
balanced_search_tree.lookup              small        bend 115.00 116.00 110.00 121.00 110.00 115.00
                                                      ref  16.58 16.60 16.77 16.45 16.63 16.81
balanced_search_tree.lookup              medium       bend 246.67 228.89 244.44 240.00 244.44 242.22
                                                      ref  37.04 37.86 29.35 37.31 37.16 37.78
balanced_search_tree.lookup              large        bend 390.38 396.15 394.23 446.15 378.85 407.69
                                                      ref  85.08 84.43 85.53 85.24 93.06 85.09
balanced_search_tree.contains            small        bend 113.75 107.50 117.50 113.75 109.38 106.88
                                                      ref  17.59 16.93 17.52 17.23 17.47 16.62
balanced_search_tree.contains            medium       bend 241.25 245.00 241.25 243.75 250.00 253.75
                                                      ref  38.23 38.23 38.21 38.56 38.28 38.26
balanced_search_tree.contains            large        bend 396.15 401.92 398.08 400.00 396.15 453.85
                                                      ref  86.13 85.77 85.78 94.34 85.24 94.93
balanced_search_tree.min                 small        bend 36.73 35.38 34.62 35.00 34.81 35.38
                                                      ref  1.03 1.03 1.02 0.99 1.06 1.00
balanced_search_tree.min                 medium       bend 104.44 106.11 109.44 110.00 108.89 107.22
                                                      ref  3.72 3.45 3.84 3.47 4.34 3.91
balanced_search_tree.min                 large        bend 134.29 222.86 94.29 228.57 316.19 59.05
                                                      ref  4.97 5.95 8.41 8.74 7.04 5.19
balanced_search_tree.max                 small        bend 40.23 44.77 43.41 42.27 42.05 44.55
                                                      ref  1.09 1.08 1.08 1.06 1.09 1.12
balanced_search_tree.max                 medium       bend 115.00 108.00 103.00 105.00 104.00 111.00
                                                      ref  3.86 3.79 3.81 3.25 4.01 3.22
balanced_search_tree.max                 large        bend 142.75 138.04 146.67 140.00 138.04 132.16
                                                      ref  4.80 4.29 3.95 4.19 4.23 4.72
balanced_search_tree.lower_bound         small        bend 107.78 106.67 116.67 105.56 113.33 115.56
                                                      ref  16.37 16.59 16.89 16.22 16.64 16.12
balanced_search_tree.lower_bound         medium       bend 260.00 257.50 260.00 252.50 245.00 255.00
                                                      ref  36.08 36.95 37.16 36.38 36.51 36.48
balanced_search_tree.lower_bound         large        bend 422.06 402.94 411.76 426.47 419.12 458.82
                                                      ref  85.09 91.86 84.49 83.56 84.41 86.12
balanced_search_tree.range               small        bend 210.94 207.81 207.81 210.94 198.44 214.06
                                                      ref  32.12 31.07 31.11 31.31 31.88 31.39
balanced_search_tree.range               medium       bend 9477.12 10065.36 9477.12 9673.20 9738.56 9673.20
                                                      ref  793.73 770.65 786.47 782.61 803.14 782.61
balanced_search_tree.range               large        bend 85937.50 103906.25 87500.00 92968.75 55468.75 86718.75
                                                      ref  8101.56 8164.06 8251.56 7917.19 8345.31 7935.94
balanced_search_tree.to_list             small        bend 558.82 666.67 568.63 573.53 573.53 593.14
                                                      ref  44.72 41.48 42.79 41.31 43.13 42.09
balanced_search_tree.to_list             medium       bend 53809.52 51428.57 50000.00 51428.57 51428.57 50952.38
                                                      ref  3314.76 3154.76 3353.33 3268.57 3295.71 3208.57
balanced_search_tree.to_list             large        bend 1764705.88 2058823.53 1823529.41 1870588.24 2023529.41 1917647.06
                                                      ref  187729.41 169282.35 190823.53 207917.65 190458.82 191529.41
balanced_search_tree.length              small        bend 1.01 1.01 1.00 1.01 0.98 0.99
                                                      ref  2.81 2.85 2.78 2.79 2.78 2.82
balanced_search_tree.length              medium       bend 1.00 0.99 0.97 1.00 1.00 0.98
                                                      ref  2.75 2.79 2.75 2.76 2.73 2.80
balanced_search_tree.length              large        bend 0.98 0.99 0.95 1.00 1.01 1.02
                                                      ref  2.74 2.74 2.75 2.74 2.74 2.74
balanced_search_tree.new                 small        bend 0.99 0.98 0.97 0.97 0.93 0.97
                                                      ref  2.39 2.41 2.39 2.39 2.43 2.39
balanced_search_tree.new                 medium       bend 0.97 0.96 0.96 0.96 0.99 0.99
                                                      ref  2.40 2.41 2.38 2.40 2.35 2.41
balanced_search_tree.new                 large        bend 0.97 0.99 0.95 1.00 0.96 1.02
                                                      ref  2.40 2.38 2.41 2.40 2.41 2.40
balanced_search_tree.new                 edge-empty   bend 0.97 0.95 0.96 0.97 0.96 0.99
                                                      ref  2.39 2.37 2.36 2.38 2.34 2.40
balanced_search_tree.length              edge-empty   bend 0.97 0.97 0.94 0.97 0.96 0.96
                                                      ref  2.64 2.71 2.65 2.70 2.69 2.70
balanced_search_tree.insert              edge-empty   bend 32.35 32.35 30.88 31.18 33.24 31.76
                                                      ref  1.49 1.48 1.48 1.49 1.49 1.47
balanced_search_tree.remove              edge-empty   bend 5.04 5.00 5.08 5.08 5.04 5.08
                                                      ref  1.00 0.99 1.00 1.00 0.99 0.99
balanced_search_tree.lookup              edge-empty   bend 3.28 3.31 3.28 3.22 3.28 3.25
                                                      ref  1.00 1.02 1.00 1.00 1.00 1.00
balanced_search_tree.contains            edge-empty   bend 3.31 3.25 3.31 3.31 3.31 3.25
                                                      ref  1.00 1.01 1.00 1.00 1.00 1.00
balanced_search_tree.min                 edge-empty   bend 3.28 3.28 3.28 3.75 3.31 3.28
                                                      ref  1.00 1.01 1.00 0.99 0.99 1.00
balanced_search_tree.max                 edge-empty   bend 3.28 3.28 3.28 3.28 3.28 3.31
                                                      ref  1.00 1.01 0.99 1.00 1.00 1.01
balanced_search_tree.lower_bound         edge-empty   bend 4.73 4.80 4.73 4.73 4.73 4.73
                                                      ref  0.99 1.01 1.00 0.99 0.99 1.00
balanced_search_tree.range               edge-empty   bend 4.18 4.22 4.18 4.18 4.22 4.22
                                                      ref  3.88 3.73 3.79 3.96 3.81 3.65
balanced_search_tree.to_list             edge-empty   bend 4.10 4.14 4.14 4.14 4.10 4.10
                                                      ref  3.41 3.37 3.34 3.30 3.38 3.33
bitset.set                               small        bend 1.45 1.43 1.45 1.43 1.45 1.43
                                                      ref  1.27 1.28 1.28 1.27 1.27 1.28
bitset.set                               medium       bend 1.32 1.31 1.32 1.33 1.31 1.29
                                                      ref  1.17 1.17 1.18 1.16 1.37 1.15
bitset.set                               large        bend 1.30 1.30 1.31 1.30 1.30 1.30
                                                      ref  1.15 1.15 1.14 1.15 1.15 1.14
bitset.clear                             small        bend 1.41 1.45 1.45 1.43 1.46 1.45
                                                      ref  1.27 1.26 1.27 1.27 1.27 1.27
bitset.clear                             medium       bend 1.30 1.29 1.29 1.29 1.29 1.28
                                                      ref  1.14 1.15 1.15 1.14 1.15 1.15
bitset.clear                             large        bend 1.29 1.29 1.45 1.29 1.29 1.28
                                                      ref  1.15 1.15 1.15 1.15 1.14 1.15
bitset.get                               small        bend 1.59 1.59 1.58 1.59 1.60 1.60
                                                      ref  1.32 1.31 1.31 1.32 1.32 1.31
bitset.get                               medium       bend 1.48 1.48 1.48 1.48 1.48 1.50
                                                      ref  1.19 1.18 1.18 1.19 1.19 1.18
bitset.get                               large        bend 1.47 1.49 1.49 1.47 1.48 1.48
                                                      ref  1.17 1.18 1.18 1.18 1.18 1.11
bitset.count                             small        bend 49.02 49.41 50.59 47.84 49.41 48.63
                                                      ref  3.89 3.94 3.88 3.88 3.87 3.90
bitset.count                             medium       bend 3025.00 2800.00 3025.00 2975.00 2900.00 2925.00
                                                      ref  191.60 184.32 184.12 185.38 184.95 184.12
bitset.count                             large        bend 181000.00 176000.00 178000.00 180000.00 179000.00 182000.00
                                                      ref  11905.00 11792.00 11900.00 11819.00 12174.00 11841.00
bitset.length                            small        bend 1.00 0.99 0.99 1.00 0.99 1.01
                                                      ref  2.74 2.81 2.71 2.76 2.72 2.76
bitset.length                            medium       bend 0.98 0.98 0.99 0.99 0.98 0.97
                                                      ref  2.70 2.72 2.75 2.73 2.69 2.74
bitset.length                            large        bend 0.99 1.00 0.97 0.97 0.97 0.99
                                                      ref  2.68 2.76 2.68 2.71 2.70 2.72
bitset.to_list                           small        bend 291.18 300.00 288.24 302.94 297.06 305.88
                                                      ref  64.66 63.80 62.91 64.59 64.56 64.49
bitset.to_list                           medium       bend 16500.00 17333.33 16000.00 17000.00 17000.00 17333.33
                                                      ref  3977.00 4074.33 4041.00 3989.50 4026.17 4014.50
bitset.to_list                           large        bend 1500000.00 1480000.00 1510000.00 1470000.00 1490000.00 1450000.00
                                                      ref  258270.00 258330.00 248470.00 258890.00 258790.00 264170.00
bitset.union                             small        bend 4.91 4.87 4.87 4.91 4.91 4.87
                                                      ref  0.99 1.01 1.00 1.03 1.15 1.03
bitset.union                             medium       bend 51.95 52.34 51.95 52.34 52.34 52.34
                                                      ref  50.23 48.73 50.21 48.61 42.96 48.52
bitset.union                             large        bend 2705.88 2764.71 2745.10 2725.49 2764.71 2764.71
                                                      ref  2833.37 2889.39 2895.80 2886.35 2878.31 2881.43
bitset.intersection                      small        bend 5.00 5.00 4.91 4.96 4.96 4.96
                                                      ref  1.04 1.13 1.13 2.05 1.20 1.03
bitset.intersection                      medium       bend 52.34 54.69 53.91 55.08 54.69 51.95
                                                      ref  49.61 48.45 50.16 48.48 49.73 48.39
bitset.intersection                      large        bend 2765.62 2734.38 2781.25 2765.62 2750.00 2765.62
                                                      ref  2894.62 2875.38 2889.72 2888.94 2876.41 2889.23
bitset.difference                        small        bend 4.96 5.00 5.00 5.00 5.00 5.00
                                                      ref  1.07 1.09 1.07 1.01 1.02 1.03
bitset.difference                        medium       bend 53.92 53.43 53.92 55.88 54.90 54.90
                                                      ref  49.71 49.64 50.16 49.50 50.60 48.97
bitset.difference                        large        bend 2812.50 2859.38 2750.00 2937.50 2984.38 2750.00
                                                      ref  2954.77 3289.66 2958.83 2965.61 3049.91 2874.33
bitset.xor                               small        bend 5.00 4.96 4.91 4.96 4.96 4.91
                                                      ref  1.01 1.18 1.03 1.01 1.00 1.02
bitset.xor                               medium       bend 55.47 55.08 54.30 55.08 55.08 55.86
                                                      ref  49.40 48.24 48.77 48.07 48.75 48.02
bitset.xor                               large        bend 2784.31 2784.31 2745.10 2764.71 2764.71 2784.31
                                                      ref  2883.78 2874.27 2880.43 2878.45 2884.45 2883.12
bitset.new                               small        bend 4.69 4.69 4.69 4.69 4.77 4.69
                                                      ref  8.07 9.70 9.19 9.18 9.49 9.14
bitset.new                               medium       bend 4.80 4.71 4.71 4.67 4.67 4.67
                                                      ref  9.68 9.17 9.18 8.95 9.21 8.39
bitset.new                               large        bend 4.69 4.69 4.73 4.69 4.69 4.78
                                                      ref  9.15 8.55 9.19 9.21 9.27 9.17
bitset.new                               edge-empty   bend 4.69 4.77 4.77 4.69 4.77 4.69
                                                      ref  9.08 8.59 8.88 8.28 9.13 8.60
bitset.length                            edge-empty   bend 0.99 1.01 1.00 1.01 0.99 1.01
                                                      ref  2.84 2.81 2.77 2.78 2.76 2.80
bitset.get                               edge-empty   bend 1.12 1.11 1.11 1.12 1.11 1.12
                                                      ref  1.01 1.01 1.01 1.01 1.01 1.01
bitset.set                               edge-empty   bend 1.12 1.12 1.12 1.12 1.12 1.12
                                                      ref  1.01 1.01 1.02 1.01 1.01 1.01
bitset.clear                             edge-empty   bend 1.10 1.12 1.10 1.11 1.12 1.12
                                                      ref  1.01 1.02 1.01 1.01 1.01 1.01
bitset.count                             edge-empty   bend 24.76 24.29 24.76 24.76 24.52 24.52
                                                      ref  3.41 3.45 3.31 3.42 3.50 3.39
bitset.union                             edge-empty   bend 4.18 4.22 4.22 4.22 4.88 3.75
                                                      ref  0.99 1.00 0.99 1.01 0.99 1.00
bitset.intersection                      edge-empty   bend 4.22 4.22 4.22 4.18 4.18 4.25
                                                      ref  0.99 1.00 0.99 0.99 1.00 1.00
bitset.difference                        edge-empty   bend 4.14 4.18 4.22 4.22 4.26 4.22
                                                      ref  1.00 0.99 0.99 0.99 0.99 1.00
bitset.xor                               edge-empty   bend 4.41 4.49 4.49 4.41 4.41 4.41
                                                      ref  1.00 1.01 1.00 0.99 0.99 0.99
bitset.to_list                           edge-empty   bend 31.67 31.17 30.50 31.00 30.83 30.83
                                                      ref  3.42 3.40 3.44 3.41 3.39 3.39
union_find.find                          small        bend 1.45 1.46 1.45 1.45 1.45 1.47
                                                      ref  1.27 1.27 1.26 1.26 1.27 1.27
union_find.find                          medium       bend 1.31 1.31 1.32 1.31 1.32 1.31
                                                      ref  1.13 1.15 1.15 1.14 1.15 1.15
union_find.find                          large        bend 1.36 1.38 1.34 1.40 1.33 1.40
                                                      ref  1.16 1.15 1.16 1.15 1.16 1.15
union_find.union                         small        bend 4.10 4.06 4.10 4.10 4.06 4.10
                                                      ref  1.57 1.49 1.60 1.50 1.56 1.49
union_find.union                         medium       bend 4.24 4.20 3.61 3.75 3.65 3.58
                                                      ref  1.30 1.32 1.30 1.32 1.30 1.33
union_find.connected                     small        bend 2.25 2.25 2.25 2.25 2.25 2.23
                                                      ref  1.57 1.58 1.61 1.60 1.58 1.55
union_find.connected                     medium       bend 2.02 2.02 2.02 2.02 2.01 2.02
                                                      ref  1.36 1.35 1.36 1.36 1.35 1.35
union_find.connected                     large        bend 2.14 2.16 2.13 2.16 2.11 2.17
                                                      ref  1.46 1.49 1.46 1.50 1.48 1.48
union_find.component_size                small        bend 1.51 1.54 1.52 1.50 1.52 1.52
                                                      ref  1.29 1.30 1.28 1.27 1.28 1.30
union_find.component_size                medium       bend 1.41 1.39 1.41 1.41 1.41 1.41
                                                      ref  1.18 1.18 1.18 1.18 1.17 1.18
union_find.component_size                large        bend 1.61 1.55 1.62 1.57 1.62 1.57
                                                      ref  1.24 1.28 1.28 1.33 1.32 1.28
union_find.component_count               small        bend 0.99 1.01 1.00 1.00 0.98 1.01
                                                      ref  2.75 2.65 2.72 2.74 2.72 2.78
union_find.component_count               medium       bend 0.98 0.99 0.99 1.00 1.00 1.00
                                                      ref  2.71 2.76 2.73 2.79 2.73 2.73
union_find.component_count               large        bend 0.99 1.01 1.00 1.01 0.98 1.01
                                                      ref  2.78 2.74 2.74 2.74 2.69 2.75
union_find.new                           small        bend 33.82 33.82 34.12 33.82 33.82 33.82
                                                      ref  1.78 1.82 1.85 1.63 1.70 1.84
union_find.new                           medium       bend 33.82 34.12 34.12 34.41 33.82 34.12
                                                      ref  1.85 1.80 1.89 1.81 1.79 1.60
union_find.new                           large        bend 34.12 34.71 33.53 35.00 34.71 34.12
                                                      ref  1.72 1.85 1.99 1.88 1.75 1.52
union_find.new                           edge-empty   bend 34.23 33.46 34.23 33.46 33.85 34.23
                                                      ref  1.84 1.80 1.88 1.77 1.80 1.81
union_find.find                          edge-empty   bend 1.10 1.11 1.12 1.12 1.12 1.11
                                                      ref  1.01 1.01 1.01 1.02 1.01 1.01
union_find.union                         edge-empty   bend 3.34 3.41 3.34 3.41 3.38 3.41
                                                      ref  1.11 1.11 1.11 1.12 1.11 1.11
union_find.connected                     edge-empty   bend 1.56 1.56 1.56 1.56 1.58 1.58
                                                      ref  1.17 1.11 1.09 1.10 1.09 1.11
union_find.component_size                edge-empty   bend 1.11 1.12 1.11 1.12 1.11 1.11
                                                      ref  1.01 1.01 1.01 1.01 1.00 1.01
union_find.component_count               edge-empty   bend 0.98 1.00 0.99 0.99 0.99 0.97
                                                      ref  2.74 2.74 2.71 2.73 2.72 2.72
fenwick_tree.add                         small        bend 76.25 73.33 74.17 73.75 73.75 73.75
                                                      ref  19.11 18.95 19.03 18.96 19.24 19.16
fenwick_tree.add                         medium       bend 200.00 205.45 200.00 200.00 200.00 196.36
                                                      ref  37.05 37.24 37.20 36.94 37.11 36.93
fenwick_tree.add                         large        bend 439.22 456.86 363.73 466.67 410.78 475.49
                                                      ref  51.46 51.96 51.57 50.67 51.49 51.40
fenwick_tree.prefix_sum                  small        bend 58.24 58.82 58.24 60.59 60.00 58.24
                                                      ref  19.05 19.15 18.86 19.42 19.09 19.75
fenwick_tree.prefix_sum                  medium       bend 150.67 146.67 148.00 148.00 152.00 148.00
                                                      ref  36.12 35.36 36.05 35.11 35.58 35.19
fenwick_tree.prefix_sum                  large        bend 326.56 340.62 292.19 348.44 303.12 349.22
                                                      ref  51.59 51.33 51.59 51.60 51.54 51.72
fenwick_tree.range_sum                   small        bend 64.00 64.00 64.00 63.33 63.67 63.33
                                                      ref  20.12 19.70 19.96 19.39 19.73 19.60
fenwick_tree.range_sum                   medium       bend 156.92 152.31 153.85 160.00 152.31 152.31
                                                      ref  37.25 36.29 36.62 35.94 36.90 36.36
fenwick_tree.range_sum                   large        bend 67.97 70.31 69.53 75.00 71.09 75.78
                                                      ref  12.31 12.06 11.99 12.28 12.00 12.10
fenwick_tree.length                      small        bend 0.98 1.00 1.01 1.02 1.01 1.01
                                                      ref  2.78 2.92 2.89 2.89 2.90 2.89
fenwick_tree.length                      medium       bend 1.01 1.00 1.01 1.00 1.01 1.01
                                                      ref  2.89 2.89 2.90 2.89 2.89 2.89
fenwick_tree.length                      large        bend 0.92 0.96 0.99 1.00 0.88 0.97
                                                      ref  2.85 2.85 2.86 2.86 3.00 2.89
fenwick_tree.from_list                   small        bend 370.00 413.33 383.33 413.33 386.67 406.67
                                                      ref  21.65 20.45 24.66 23.94 23.14 19.28
fenwick_tree.from_list                   medium       bend 380.00 423.33 376.67 390.00 396.67 440.00
                                                      ref  21.10 23.53 22.23 23.04 23.42 22.73
fenwick_tree.from_list                   large        bend 409.38 406.25 389.84 416.41 399.22 367.97
                                                      ref  23.40 21.56 22.50 23.36 23.40 21.39
fenwick_tree.new                         small        bend 3.35 3.38 4.20 3.77 3.95 3.94
                                                      ref  9.23 10.38 10.06 11.06 9.58 9.93
fenwick_tree.new                         medium       bend 3.82 3.79 3.66 3.92 3.92 3.89
                                                      ref  9.43 9.92 10.35 10.44 10.40 10.06
fenwick_tree.new                         large        bend 3.49 3.55 3.25 3.71 3.33 3.51
                                                      ref  9.74 8.80 8.76 7.68 9.82 9.46
fenwick_tree.new                         edge-empty   bend 3.41 3.41 3.41 3.34 3.38 3.47
                                                      ref  8.47 9.22 9.43 8.51 9.58 9.48
fenwick_tree.from_list                   edge-empty   bend 360.00 370.00 363.33 356.67 366.67 360.00
                                                      ref  20.62 22.65 22.32 19.88 22.80 21.27
fenwick_tree.length                      edge-empty   bend 0.99 1.01 0.99 1.01 0.99 0.99
                                                      ref  2.85 2.83 2.85 2.81 2.86 2.83
fenwick_tree.add                         edge-empty   bend 3.41 3.44 3.44 3.44 3.47 3.41
                                                      ref  1.01 1.01 1.02 1.01 1.01 1.01
fenwick_tree.prefix_sum                  edge-empty   bend 5.98 5.98 5.98 5.98 5.98 5.98
                                                      ref  1.04 1.05 1.04 1.06 1.05 1.04
fenwick_tree.range_sum                   edge-empty   bend 6.25 5.62 6.25 5.42 6.88 6.09
                                                      ref  1.49 1.50 1.49 1.48 1.48 1.48
segment_tree.range_add                   small        bend 96.19 97.14 100.00 99.05 99.05 101.90
                                                      ref  27.40 26.55 26.68 26.55 26.64 26.34
segment_tree.range_add                   medium       bend 238.24 241.18 236.76 238.24 239.71 245.59
                                                      ref  51.29 50.66 51.16 50.71 50.57 51.04
segment_tree.range_add                   large        bend 101.56 113.28 98.44 125.78 97.66 117.19
                                                      ref  20.34 19.89 20.44 20.20 20.21 19.98
segment_tree.get                         small        bend 52.94 53.73 52.94 52.94 52.55 52.94
                                                      ref  3.28 3.24 3.26 3.24 3.19 3.27
segment_tree.get                         medium       bend 138.46 139.42 139.42 138.46 143.27 138.46
                                                      ref  5.97 5.96 6.02 5.98 6.01 6.06
segment_tree.get                         large        bend 275.00 371.88 279.69 353.12 331.25 354.69
                                                      ref  9.60 9.25 9.45 10.02 10.30 9.09
segment_tree.range_query                 small        bend 63.53 62.35 63.53 63.14 62.35 61.96
                                                      ref  20.42 20.22 20.63 19.92 20.29 19.83
segment_tree.range_query                 medium       bend 154.41 154.41 155.88 144.12 154.41 152.94
                                                      ref  37.76 37.79 38.02 37.17 37.49 36.82
segment_tree.range_query                 large        bend 71.09 76.56 67.58 79.69 70.31 81.25
                                                      ref  12.61 12.52 12.37 12.54 12.53 12.59
segment_tree.length                      small        bend 1.00 1.00 1.03 1.00 0.98 1.01
                                                      ref  2.90 2.88 2.89 2.83 2.80 2.81
segment_tree.length                      medium       bend 1.02 1.00 0.99 0.99 0.99 1.02
                                                      ref  2.77 2.81 2.74 2.81 2.73 2.78
segment_tree.length                      large        bend 0.94 1.01 0.95 0.99 0.93 0.97
                                                      ref  2.77 2.74 2.75 2.79 2.74 2.72
segment_tree.set                         small        bend 86.15 87.69 88.46 86.92 88.46 88.46
                                                      ref  8.24 8.28 8.30 8.24 8.25 8.23
segment_tree.set                         medium       bend 232.69 228.85 234.62 230.77 230.77 228.85
                                                      ref  17.63 17.83 17.71 18.00 17.82 17.70
segment_tree.set                         large        bend 425.00 918.75 509.38 601.56 418.75 509.38
                                                      ref  44.73 96.83 44.36 43.23 43.85 43.42
segment_tree.from_list                   small        bend 468.94 531.75 409.38 448.25 409.25 470.62
                                                      ref  59.59 53.22 50.99 51.75 50.73 59.14
segment_tree.from_list                   medium       bend 440.00 464.00 448.00 440.00 432.00 456.00
                                                      ref  50.63 58.88 49.48 56.92 52.34 51.03
segment_tree.from_list                   large        bend 393.33 406.67 400.00 416.67 393.33 400.00
                                                      ref  52.68 48.22 54.09 50.12 51.08 48.92
segment_tree.new                         small        bend 3.49 3.49 3.83 3.46 3.54 3.52
                                                      ref  9.46 9.42 9.30 9.43 9.96 8.64
segment_tree.new                         medium       bend 3.46 3.52 3.46 3.52 3.49 3.52
                                                      ref  9.86 9.47 9.44 9.31 9.42 9.37
segment_tree.new                         large        bend 3.49 3.85 3.06 3.61 3.45 3.45
                                                      ref  9.31 10.46 9.85 9.42 9.92 9.33
segment_tree.new                         edge-empty   bend 3.50 3.44 3.50 3.47 3.50 3.56
                                                      ref  9.56 9.33 8.47 9.21 9.46 9.18
segment_tree.from_list                   edge-empty   bend 406.67 400.00 413.33 396.67 423.33 416.67
                                                      ref  52.91 52.17 51.74 50.40 51.28 52.18
segment_tree.length                      edge-empty   bend 1.66 1.00 0.99 1.01 1.02 1.34
                                                      ref  2.90 2.87 2.82 2.89 2.91 2.95
segment_tree.get                         edge-empty   bend 3.38 3.50 3.28 3.34 3.28 3.44
                                                      ref  1.05 1.11 1.08 1.06 1.28 1.04
segment_tree.set                         edge-empty   bend 3.83 3.52 3.09 3.42 3.46 3.48
                                                      ref  1.00 1.03 1.02 1.02 1.02 1.01
segment_tree.range_query                 edge-empty   bend 6.13 5.27 7.54 6.52 6.91 5.00
                                                      ref  1.50 1.49 1.51 1.51 1.50 1.49
segment_tree.range_add                   edge-empty   bend 6.67 6.72 6.77 6.77 6.67 6.77
                                                      ref  2.64 2.69 2.50 2.50 2.51 2.69
prefix_trie.insert                       small        bend 560.00 688.00 876.00 680.00 684.00 704.00
                                                      ref  116.19 111.20 115.90 113.26 140.65 117.56
prefix_trie.insert                       medium       bend 413.33 503.33 430.00 480.00 426.67 476.67
                                                      ref  96.91 95.65 97.25 95.22 97.05 96.03
prefix_trie.lookup                       small        bend 220.00 220.00 218.00 218.00 222.00 216.00
                                                      ref  24.55 23.64 25.35 23.72 24.65 23.71
prefix_trie.lookup                       medium       bend 300.00 306.67 310.00 293.33 310.00 336.67
                                                      ref  45.12 44.78 46.80 44.76 49.54 41.54
prefix_trie.lookup                       large        bend 431.25 571.88 487.50 531.25 481.25 506.25
                                                      ref  93.98 85.44 99.28 84.09 85.95 83.44
prefix_trie.remove                       small        bend 234.00 222.00 220.00 268.00 226.00 234.00
                                                      ref  24.45 25.79 24.47 24.39 24.55 24.59
prefix_trie.remove                       medium       bend 326.67 333.33 313.33 333.33 310.00 330.00
                                                      ref  50.35 46.94 46.93 46.67 45.10 46.27
prefix_trie.contains                     small        bend 226.00 224.00 226.00 226.00 220.00 220.00
                                                      ref  25.82 24.98 26.74 24.76 25.94 24.72
prefix_trie.contains                     medium       bend 313.33 313.33 303.33 318.33 310.00 308.33
                                                      ref  43.83 46.99 45.95 44.24 46.30 45.28
prefix_trie.contains                     large        bend 492.19 585.94 500.00 612.50 468.75 546.88
                                                      ref  84.42 84.81 84.00 84.61 94.67 89.16
prefix_trie.prefix_entries               small        bend 1047.06 1094.12 1070.59 1076.47 1064.71 1105.88
                                                      ref  72.52 72.97 78.85 73.06 75.92 67.40
prefix_trie.prefix_entries               medium       bend 34000.00 37666.67 35666.67 37000.00 35666.67 39000.00
                                                      ref  2087.00 1840.00 1904.33 1898.33 1913.33 1826.33
prefix_trie.prefix_entries               large        bend 831250.00 1212500.00 887500.00 1237500.00 931250.00 1068750.00
                                                      ref  33312.50 30337.50 25787.50 24706.25 32293.75 24093.75
prefix_trie.longest_prefix               small        bend 190.00 190.00 188.33 188.33 190.00 188.33
                                                      ref  26.83 26.13 26.79 26.07 26.73 26.43
prefix_trie.longest_prefix               medium       bend 255.88 255.88 255.88 251.47 264.71 257.35
                                                      ref  48.45 47.33 48.85 49.06 47.64 46.90
prefix_trie.longest_prefix               large        bend 393.75 479.69 428.12 464.06 412.50 462.50
                                                      ref  103.93 98.23 94.95 95.38 92.93 93.99
prefix_trie.new                          small        bend 1.00 1.01 1.01 1.00 1.00 1.01
                                                      ref  2.52 2.54 2.63 2.52 2.54 2.52
prefix_trie.new                          medium       bend 1.02 1.02 1.02 1.01 1.01 1.02
                                                      ref  2.53 2.53 2.53 2.53 2.53 2.51
prefix_trie.new                          large        bend 0.95 1.06 0.95 1.06 0.95 1.03
                                                      ref  2.53 2.50 2.54 2.55 2.55 2.56
prefix_trie.new                          edge-empty   bend 1.02 0.99 1.01 1.00 1.01 1.01
                                                      ref  2.53 2.51 2.55 2.53 2.52 2.53
prefix_trie.insert                       edge-empty   bend 866.67 1236.67 890.00 1233.33 823.33 1186.67
                                                      ref  192.54 202.51 192.88 172.11 202.61 170.38
prefix_trie.lookup                       edge-empty   bend 140.00 137.50 137.50 137.50 140.00 137.50
                                                      ref  1.25 1.32 1.26 1.34 1.25 1.26
prefix_trie.remove                       edge-empty   bend 137.50 137.50 136.25 136.25 133.75 138.75
                                                      ref  1.26 1.31 1.24 1.27 1.27 1.27
prefix_trie.contains                     edge-empty   bend 142.86 141.43 141.43 142.86 134.29 167.14
                                                      ref  1.28 1.30 1.28 1.29 1.34 0.80
prefix_trie.prefix_entries               edge-empty   bend 20.39 28.04 24.31 22.75 23.73 25.49
                                                      ref  3.79 3.95 3.62 3.82 4.19 3.65
prefix_trie.longest_prefix               edge-empty   bend 151.43 142.86 158.57 160.00 162.86 145.71
                                                      ref  3.00 2.97 2.77 2.86 2.88 2.24
graph.add_vertex                         small        bend 176.19 135.24 168.57 139.05 146.67 143.81
                                                      ref  15.96 18.66 17.10 17.57 17.72 17.69
graph.add_vertex                         medium       bend 276.19 230.95 233.33 264.29 421.43 221.43
                                                      ref  29.83 29.18 28.96 27.44 32.97 27.56
graph.add_vertex                         large        bend 342.31 284.62 307.69 365.38 271.15 363.46
                                                      ref  40.77 40.77 41.81 40.69 39.21 39.88
graph.remove_vertex                      small        bend 7.57 15.26 8.48 8.00 4.94 4.58
                                                      ref  1.04 0.87 0.96 1.17 1.75 0.96
graph.remove_vertex                      large        bend 300000.00 302500.00 292500.00 287500.00 277500.00 312500.00
                                                      ref  39112.50 38342.50 37162.50 37140.00 38667.50 41480.00
graph.add_edge                           small        bend 1690.00 1640.00 1710.00 1670.00 1720.00 2050.00
                                                      ref  75.95 73.32 76.24 72.97 78.85 76.92
graph.add_edge                           medium       bend 4025.00 4150.00 5075.00 6950.00 6200.00 6025.00
                                                      ref  343.27 345.62 540.77 490.77 530.38 439.90
graph.add_edge                           large        bend 4733.33 5566.67 5000.00 5233.33 4833.33 5433.33
                                                      ref  470.87 490.00 522.97 450.50 498.43 460.60
graph.remove_edge                        small        bend 335.00 315.00 320.00 318.33 325.00 311.67
                                                      ref  43.46 41.02 42.32 45.47 52.65 38.39
graph.remove_edge                        medium       bend 568.75 487.50 512.50 481.25 487.50 506.25
                                                      ref  75.76 69.49 73.50 71.92 71.48 68.31
graph.remove_edge                        large        bend 703.85 703.85 673.08 707.69 700.00 723.08
                                                      ref  105.52 98.06 114.90 104.12 107.18 100.82
graph.has_vertex                         small        bend 118.67 117.33 117.33 120.00 121.33 119.33
                                                      ref  17.41 17.04 18.20 17.36 18.37 16.56
graph.has_vertex                         medium       bend 215.38 213.46 213.46 213.46 217.31 394.23
                                                      ref  33.07 31.43 32.49 32.38 36.52 43.26
graph.has_vertex                         large        bend 458.82 456.86 443.14 435.29 396.08 533.33
                                                      ref  62.92 56.25 57.81 55.88 61.78 72.01
graph.has_edge                           small        bend 448.00 428.00 440.00 480.00 472.00 476.00
                                                      ref  58.30 56.10 60.47 57.90 63.91 55.40
graph.has_edge                           medium       bend 718.75 787.50 793.75 768.75 718.75 762.50
                                                      ref  112.11 107.46 112.41 109.62 111.63 107.66
graph.has_edge                           large        bend 1209.09 1200.00 1200.00 1272.73 1281.82 1745.45
                                                      ref  167.92 161.06 163.87 192.24 219.35 205.00
graph.neighbors                          small        bend 317.14 340.00 305.71 322.86 342.86 325.71
                                                      ref  38.51 38.26 35.17 38.79 37.87 36.07
graph.neighbors                          medium       bend 509.09 481.82 472.73 468.18 477.27 500.00
                                                      ref  66.56 58.80 70.92 58.37 67.62 59.87
graph.neighbors                          large        bend 580.00 553.33 953.33 660.00 646.67 660.00
                                                      ref  108.57 102.63 111.60 95.03 94.09 86.99
graph.vertices                           small        bend 1260.00 1400.00 1393.33 1553.33 1480.00 1460.00
                                                      ref  64.65 59.70 64.09 55.14 37.21 50.20
graph.vertices                           medium       bend 20800.00 20600.00 20400.00 23400.00 20200.00 19200.00
                                                      ref  735.60 1170.20 899.00 1054.80 903.20 843.20
graph.vertices                           large        bend 228000.00 230000.00 186000.00 184000.00 180000.00 206000.00
                                                      ref  7390.00 7056.00 7798.00 7274.00 7986.00 7330.00
graph.edges                              small        bend 3433.33 3733.33 3666.67 4100.00 3500.00 3433.33
                                                      ref  174.23 188.47 175.93 184.83 203.23 164.73
graph.edges                              medium       bend 76666.67 76666.67 73333.33 76666.67 74666.67 76000.00
                                                      ref  3717.33 3968.00 4261.33 3848.67 3624.67 3840.67
graph.edges                              large        bend 1013333.33 756666.67 750000.00 820000.00 833333.33 843333.33
                                                      ref  34116.67 32153.33 34086.67 31723.33 34170.00 29136.67
graph.new                                small        bend 5.44 6.23 6.08 6.52 5.39 6.47
                                                      ref  2.52 2.44 2.63 2.31 2.65 2.37
graph.new                                medium       bend 5.94 6.61 5.16 7.66 7.08 6.72
                                                      ref  2.44 2.45 2.75 2.98 2.99 2.70
graph.new                                large        bend 6.25 6.67 5.57 6.15 5.62 6.51
                                                      ref  2.66 2.38 2.44 2.45 2.44 2.45
graph.new                                edge-empty   bend 5.78 6.47 5.44 6.47 6.08 6.57
                                                      ref  2.52 2.33 2.51 2.34 2.52 2.27
graph.add_vertex                         edge-empty   bend 36.47 32.94 34.71 36.47 33.53 50.29
                                                      ref  1.59 1.58 1.61 1.60 1.79 1.86
graph.remove_vertex                      edge-empty   bend 10.16 10.31 9.92 10.31 10.00 12.89
                                                      ref  1.54 1.39 1.67 1.49 1.72 1.70
graph.add_edge                           edge-empty   bend 17.65 20.10 22.94 18.53 19.61 19.31
                                                      ref  1.62 1.55 1.81 4.93 1.74 1.49
graph.remove_edge                        edge-empty   bend 16.56 16.72 15.78 24.22 26.41 22.19
                                                      ref  1.55 1.53 1.71 1.81 1.94 1.90
graph.has_vertex                         edge-empty   bend 10.23 9.69 10.31 10.47 9.69 10.78
                                                      ref  1.75 1.88 1.74 1.76 1.54 1.91
graph.has_edge                           edge-empty   bend 20.20 22.75 20.00 21.96 25.49 22.55
                                                      ref  1.76 1.76 2.31 2.63 1.78 1.71
graph.neighbors                          edge-empty   bend 14.69 15.39 13.12 28.05 19.92 13.98
                                                      ref  1.74 2.18 1.75 2.88 1.62 1.92
graph.vertices                           edge-empty   bend 12.92 8.18 9.58 10.16 8.80 7.81
                                                      ref  4.74 5.30 4.65 4.01 4.56 4.57
graph.edges                              edge-empty   bend 11.09 16.05 12.11 14.92 11.64 13.20
                                                      ref  4.42 7.72 0.08 3.35 4.95 4.46
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
dynamic_array.push / large: sample 2: A-B = -91000000ns (bend) / 26414000ns (reference), below the 50000000ns / 100000ns minima
dynamic_array.pop / small: sample 0: A-B = -243000000ns (bend) / 130340000ns (reference), below the 50000000ns / 100000ns minima
dynamic_array.pop / medium: sample 3: A-B = -642000000ns (bend) / 418200000ns (reference), below the 50000000ns / 100000ns minima
dynamic_array.pop / large: sample 0: A-B = -89000000ns (bend) / 325008000ns (reference), below the 50000000ns / 100000ns minima
deque.push_front / large: sample 5: A-B = 37000000ns (bend) / 12498000ns (reference), below the 50000000ns / 100000ns minima
deque.push_back / large: sample 5: A-B = 1294000000ns (bend) / -7518000ns (reference), below the 50000000ns / 100000ns minima
deque.pop_back / small: A-B stayed at -1471000000ns (bend) / 178248000ns (reference) at the round cap count=32 reps=4194304 (bend region A 6430ms), below the 50000000ns / 100000ns minima
deque.pop_back / medium: a single Bend region already takes 21645ms at count=2048 reps=192512 while A-B is only -812000000ns, so the row cannot be sampled 6 times within the per-row budget
deque.pop_back / large: sample 0: A-B = -84000000ns (bend) / 768430000ns (reference), below the 50000000ns / 100000ns minima
doubly_linked_list.new / large: sample 0: A-B = 48000000ns (bend) / 252449000ns (reference), below the 50000000ns / 100000ns minima
binary_heap.push / large: a single Bend region already takes 33838ms at count=20000 reps=128 while A-B is only -3235000000ns, so the row cannot be sampled 6 times within the per-row budget
binary_heap.pop / medium: sample 1: A-B = 42000000ns (bend) / 9313000ns (reference), below the 50000000ns / 100000ns minima
balanced_search_tree.remove / medium: sample 0: A-B = 49000000ns (bend) / 30100000ns (reference), below the 50000000ns / 100000ns minima
balanced_search_tree.remove / large: sample 3: A-B = -1356000000ns (bend) / 59198000ns (reference), below the 50000000ns / 100000ns minima
union_find.union / large: sample 2: A-B = -97000000ns (bend) / 3897000ns (reference), below the 50000000ns / 100000ns minima
prefix_trie.insert / large: sample 5: A-B = -106000000ns (bend) / 76471000ns (reference), below the 50000000ns / 100000ns minima
prefix_trie.remove / large: sample 0: A-B = -31000000ns (bend) / 58587000ns (reference), below the 50000000ns / 100000ns minima
graph.remove_vertex / medium: sample 0: A-B = 39000000ns (bend) / 22619000ns (reference), below the 50000000ns / 100000ns minima
```

Raw per-sample log: `build/bench/logs/samples.log`;
machine-readable evidence with source and artifact hashes:
`build/performance/report.json`.
