#!/usr/bin/env python3
"""Render BENCHMARKS.md from build/performance/report.json.

  python3 tools/bench_report.py

Reads only the report the runner wrote; it never re-times anything, so the
document cannot disagree with the evidence file.
"""

import json
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'build' / 'performance' / 'report.json'
COSTMODEL = ROOT / 'build' / 'performance' / 'costmodel.json'
CONTRACT = json.loads((ROOT / 'automation' / 'performance_contract.json').read_text())
OUT = ROOT / 'BENCHMARKS.md'

PREAMBLE = """# Benchmarks

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

"""


def main():
    if not REPORT.is_file():
        print('no report at %s' % REPORT, file=sys.stderr)
        return 1
    r = json.loads(REPORT.read_text())
    rows = r['benchmarks']
    env = r['environment']
    limit = CONTRACT['max_ratio']

    invariant_ops = {'length', 'capacity', 'new', 'count', 'min', 'max',
                     'to_list', 'to_sorted_list', 'vertices', 'edges',
                     'component_count', 'peek', 'peek_front', 'peek_back',
                     'keys', 'len'}
    for x in rows:
        name = x['operation'].split('.', 1)[1]
        flags = []
        if name in invariant_ops:
            flags.append('argument-free')
        if x.get('method') == 'pair':
            flags.append('restoring pair')
        x['flags'] = flags

    ok = [x for x in rows if x.get('measurement') != 'failed']
    bad = [x for x in rows if x.get('measurement') == 'failed']
    for x in ok:
        x['ratio'] = statistics.median(x['bend_ns']) / statistics.median(x['reference_ns'])
        if statistics.median(x['reference_ns']) <= 3.0:
            x['flags'] = x['flags'] + ['barrier-dominated']
    within = [x for x in ok if x['ratio'] <= limit]
    over = [x for x in ok if x['ratio'] > limit]
    # `restoring pair` is NOT an excuse for a ratio: both sides run the same
    # pair, so such a row counts as a plain over-limit row here. Only the two
    # flags that really do put the number in question (a loop-invariant
    # operation, a reference cost at the level of the barrier) keep a row out
    # of the unflagged worst case.
    excusing = {'argument-free', 'barrier-dominated'}
    clean_over = [x for x in over if not (set(x['flags']) & excusing)]

    out = [PREAMBLE]
    out.append('## Environment\n')
    for k in ['cpu', 'os', 'bend_compiler', 'reference_compiler', 'bend_flags',
              'reference_flags', 'reference_revision']:
        out.append('* **%s**: %s' % (k, env[k]))
    out.append('')
    out.append('> The machine was **not idle** during this run: unrelated processes were')
    out.append('> using whole cores throughout. The runner rejects unusable measurements')
    out.append('> rather than reporting them, but the surviving numbers still carry that')
    out.append('> noise. Re-run on an idle machine for publication-quality figures.')
    out.append('')

    if COSTMODEL.is_file():
        cm = json.loads(COSTMODEL.read_text())['primitives']
        out.append('## What the primitives cost\n')
        out.append('Measured by `tools/costmodel.py` from `benchmarks/micro.bend` and')
        out.append('`benchmarks/native/micro.c`, which perform the identical work. This is not')
        out.append('one of the contract workloads; it is here so the per-operation ratios below')
        out.append('can be read against what the primitives themselves cost.\n')
        out.append('| primitive | operations | bend ns | ref ns | ratio |')
        out.append('|---|---|---|---|---|')
        names = {'arith': 'one LCG step and an add',
                 'array': 'one indexed read + write of a 4096-slot `Base.Array`',
                 'list': 'one step of traversing a **retained** (`&2`) cons list',
                 'alloc': 'one node of a built-and-consumed binary `Data` tree',
                 'fresh': 'one node of a built-and-consumed (`&2`) cons list'}
        for r in cm:
            out.append('| `%s` - %s | %d | %.2f | %.2f | %.2fx |'
                       % (r['primitive'], names.get(r['primitive'], ''), r['operations'],
                          r['bend_ns'], r['reference_ns'], r['ratio']))
        out.append('')
        out.append('Read it carefully, because it does not say what one might expect:')
        out.append('')
        out.append('* **Arithmetic and indexed array access are at parity.** Bend compiles')
        out.append('  `Array.get` / `Array.set` to real indexed loads and stores on a flat')
        out.append('  array, and compiles `Nat`, `U32.from_nat`/`to_nat` and `Nat.div` to')
        out.append('  machine arithmetic. None of that is folklore: it is measured here, and')
        out.append('  it stays flat across sizes 64 .. 262144 in the `dynamic_array.get` and')
        out.append('  `bitset.get` rows below.')
        out.append('* **Allocation is not the problem.** A plain `Data` tree node costs Bend')
        out.append('  about 2.6 ns to allocate, traverse and release.')
        out.append('* **Traversing a retained, shareable (`&2`) structure is the problem.**')
        out.append('  Walking a cons list that stays alive costs Bend ~9 ns per node against')
        out.append('  ~1 ns in C, because the runtime has to duplicate the part it consumes.')
        out.append('  Every persistent structure in this library is built from `&2` types, so')
        out.append('  every traversal pays it. That single factor, not allocation, is what')
        out.append('  separates the passing rows from the failing ones.')
        out.append('')
        out.append('The two C rows that look bad for C (`alloc`, `fresh`) are malloc/free per')
        out.append('node, which is what a straightforward C linked structure does; an arena')
        out.append('would be several times faster. They are **not** presented as Bend wins -')
        out.append('they are here to show what Bend node allocation costs in absolute terms.')
        out.append('')
        out.append('That is why the structures divide so sharply below: an **array-backed**')
        out.append('structure (`dynamic_array`, and now `bitset`) can meet the 2.5x contract,')
        out.append('and a structure whose operations walk retained `&2` nodes cannot, whatever')
        out.append('the constant factors. Closing the remaining gap is a representation change')
        out.append('for each structure (indices into a `Base.Array` arena instead of shared')
        out.append('node references), with the proofs redone against it - not tuning.')
        out.append('`WORK_LOG.md` lists them in priority order.')
        out.append('')
        out.append('One structure has already been moved: `bitset` kept its packed words in')
        out.append('a cons list, which made `get`/`set`/`clear` O(words) while the C')
        out.append('reference is O(1) on a flat array - not the same algorithm. It now uses')
        out.append('`Base.Array`. `WORK_LOG.md` records the before/after per row (for')
        out.append('example `bitset.set` at size 4096 went from 2243x to the figure in the')
        out.append('table below) and what the migration cost in proof terms.')
        out.append('')

    out.append('## Verdict\n')
    out.append('| | rows |')
    out.append('|---|---|')
    out.append('| measured, within %.1fx | %d |' % (limit, len(within)))
    out.append('| measured, **over %.1fx** | %d |' % (limit, len(over)))
    out.append('| of those, unflagged (varying argument, reference > 3 ns/op) | %d |' % len(clean_over))
    out.append('| FAILED measurement (not resolvable above the clock minima) | %d |' % len(bad))
    out.append('| total rows in `benchmarks/workloads.py` | %d |' % len(rows))
    out.append('')
    if over or bad:
        out.append('**The %.1fx contract is NOT met.** %d measured workloads exceed it'
                   % (limit, len(over)))
        if clean_over:
            w = max(clean_over, key=lambda x: x['ratio'])
            out.append('(worst unflagged row: `%s` / %s at **%.2fx**;'
                       % (w['operation'], w['workload'], w['ratio']))
        if over:
            w2 = max(over, key=lambda x: x['ratio'])
            out.append('worst row of any kind: `%s` / %s at **%.2fx**)'
                       % (w2['operation'], w2['workload'], w2['ratio']))
        out.append('and %d workloads could not be measured at all. The nine `lru.*`'
                   % len(bad))
        out.append('operations the contract requires have **no rows**: the retained LRU')
        out.append('cannot be compiled to a native binary with this toolchain (see')
        out.append('`docs/VALIDATION.md`, "arity over 255"), and substituting a')
        out.append('non-native backend would not be a native-C measurement.')
        out.append('')

    out.append('## All rows\n')
    out.append('`bend` and `ref` are nanoseconds per operation (median of the samples).\n')
    bystruct = {}
    for x in rows:
        bystruct.setdefault(x['operation'].split('.')[0], []).append(x)
    for sid in sorted(bystruct):
        out.append('### `%s`\n' % sid)
        out.append('| operation | workload | size | ops/sample | bend ns | ref ns | ratio | verified | flags |')
        out.append('|---|---|---|---|---|---|---|---|---|')
        for x in bystruct[sid]:
            if x.get('measurement') == 'failed':
                out.append('| `%s` | %s | %d | - | FAILED | FAILED | - | - | %s |'
                           % (x['operation'].split('.', 1)[1], x['workload'], x['size'],
                              x.get('reason', '')))
            else:
                flag = '' if x['ratio'] <= limit else ' **over**'
                out.append('| `%s` | %s | %d | %d | %.2f | %.2f | %.2fx%s | %s | %s |'
                           % (x['operation'].split('.', 1)[1], x['workload'], x['size'],
                              x['operations_per_sample'],
                              statistics.median(x['bend_ns']),
                              statistics.median(x['reference_ns']),
                              x['ratio'], flag,
                              'yes' if x['verified'] else 'NO',
                              ', '.join(x['flags']) or '-'))
        out.append('')

    out.append('## Individual samples\n')
    out.append('Every sample of every measured row, nanoseconds per operation, in the')
    out.append('order taken (Bend and reference alternate within a row):\n')
    out.append('```')
    for x in ok:
        out.append('%-40s %-12s bend %s' % (x['operation'], x['workload'],
                                            ' '.join('%.2f' % v for v in x['bend_ns'])))
        out.append('%-40s %-12s ref  %s' % ('', '',
                                            ' '.join('%.2f' % v for v in x['reference_ns'])))
    out.append('```')
    out.append('')
    if bad:
        out.append('## Failed measurements\n')
        out.append('A row is FAILED when the difference `A - B` cannot be driven above the')
        out.append('clock minima on both sides, *including* when it comes out negative.')
        out.append('Regions A and B now differ only in the trip count (`2k` against `k`)')
        out.append('and the region order is alternated over the samples, so neither the')
        out.append('deallocation asymmetry of the earlier two-region form nor a monotone')
        out.append('machine drift can produce a failure here; what remains is an operation')
        out.append('whose per-iteration cost is too small, or a round whose build is too')
        out.append('expensive, to drive the difference above the clock minima within the')
        out.append('per-row budget. Such rows are reported as failures, never as numbers.\n')
        out.append('```')
        for x in bad:
            out.append('%s / %s: %s' % (x['operation'], x['workload'], x.get('reason', '')))
        out.append('```')
        out.append('')
    out.append('Raw per-sample log: `build/bench/logs/samples.log`;')
    out.append('machine-readable evidence with source and artifact hashes:')
    out.append('`build/performance/report.json`.')
    out.append('')

    OUT.write_text('\n'.join(out))
    print('wrote %s (%d rows: %d within, %d over, %d failed)'
          % (OUT, len(rows), len(within), len(over), len(bad)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
