## Operator correction — destructive A/B timing

My prior suggestion of count=1 alone is insufficient under BENCH_REGIONS:
region A executes 2*count and B executes count on the same state, so A-B can
measure a second empty purge/no-op resize. Do NOT integrate that version.
For isolated destructive-operation rows, prepare independent identical cache
states for every measured call before the operation loop, with identical total
preparation in A/B/C (use total count + nulls consistently); execute each purge
or shrinking resize on its own nonempty cache. Preserve equivalent final drain
and checksum checks. Calibrate via whole rounds and make preparation explicit.
Alternatively retain paired diagnostics with accurate labels, but these cannot
establish isolated operation acceptance. Canonical rows remain pending review;
existing 408 rows and reference files stay unchanged. This supersedes only the
count=1 recipe, not the requirement to measure real destructive operations.

## Operator follow-up review — isolated LRU costs

The optimized O(1) recency/open-addressed C design addresses the rejected
reference architecture. Integration still awaits completed differential and
sanitizer results. The new rows are not yet approved as written: selectors
11/12 include purge/resize PLUS refill. Equal logical refill work on both sides
does NOT imply the timing ratio is unaffected: refill can dominate and mask the
operation ratio. Remove that claim. Keep refill pairs only as clearly labeled
diagnostic rows; do not claim isolated purge/resize acceptance from them.
For canonical nonempty purge/resize rows use one actual call per freshly built
round (selectors 5/6, count=1, grow=reps), retaining canonical region timing and
reporting an unmeasurable row honestly if calibration cannot resolve it. Existing
rows remain untouched. Mark any paired diagnostic method accurately as pair.
Finish sanitizer/checksum sweep before submitting the addition for integration.

OPERATOR REJECTION — LRU REFERENCE, 2026-09-21: Your new native/lru.c intentionally uses O(n) singly linked recency scans because the old Bend cache does. This is REJECTED for acceptance. The user explicitly requires genuinely optimized C algorithms/layouts and bringing Bend to their equivalent, not forcing C to imitate current Bend overhead. Use indexed/intrusive doubly linked recency with O(1) detach/touch/evict and efficient lookup. Retain native Bend Map as requested; design the efficient Bend recency storage and prove the port, preserving behavior. A slow algorithm does not become an optimized baseline by matching the current implementation. Do not present this rejected C reference as accepted; its copy is quarantined in docs/archive. Existing 18 pinned files remain unchanged.

Rebuild the new LRU C reference from an efficient design and compare it honestly with the Bend implementation, documenting lookup differences. Also fix C key initialization: key_of writes a prefix but memcpy/first_diff read all KEYMAX bytes, so initialize the entire buffer and validate with sanitizer/checksum/differential tests. Audit workload semantics: purge/resize rows must really use whole-round growth rather than default size-preserving calibration; repeated purge/resize must not predominantly benchmark an empty/no-op cache without explicit rows. New must perform observable construction work. Prepare corrected additive rows; do not edit canonical workloads yet. Original scope includes all graph/DLL/other proof and performance gaps: continue the entire task with these requirements and no early milestone stop.

## Operator review — 2026-09-21 04:31 Zurich

Adding missing LRU coverage is within the user objective. The active objective
protects an explicit list of existing C files, NOT the whole native directory.
A NEW benchmarks/native/lru.c is already editable: implement a genuinely optimized
C reference and the Bend driver, preserving native-Map LRU semantics, no callbacks
or concurrency. Existing pinned C references must remain byte-identical.

Prepare the additive workload rows as benchmarks/experiments/lru_workloads.py or
an append-only patch for benchmarks/workloads.py; document selectors, counts,
size-changing behavior and checksum equivalence. The operator will review and
apply the concrete addition and update the pin. Do not edit canonical workloads
or relax any existing row. Continue all missing implementation/proof work while
that concrete addition is prepared. No existing C slowdown or threshold change
is approved. Supplemental graph enumeration experiments may be reported separately;
they cannot replace canonical rows. Deque calibration change is not yet approved.

# Benchmark change proposal (for operator review)

Written under the rule: "If a genuine harness defect or new LRU coverage
requires a change, write a concrete proposal with evidence in
docs/BENCHMARK_CHANGE_PROPOSAL.md, leave canonical files unchanged, and
continue implementation/proofs while the operator reviews it."

Nothing in this document has been applied. `benchmarks/run.py`,
`benchmarks/workloads.py`, `benchmarks/native/*.c`, `benchmarks/native/*.h`
and `docs/BENCHMARK_INTEGRITY.md` are unchanged.

---

## 1. The nine required `lru.*` rows need protected-file changes (BLOCKING)

`automation/performance_contract.json` requires `lru.add`, `lru.get`,
`lru.peek`, `lru.contains`, `lru.remove`, `lru.purge`, `lru.resize`,
`lru.keys` and `lru.len`. No such rows exist, so
`automation/performance_gate.py` fails with missing operations regardless of
every other result.

Two things are needed and BOTH are outside the editable scope:

1. `benchmarks/workloads.py` (protected) must gain the `lru.*` rows —
   small/medium/large plus an edge case per operation, in the same shape as
   the other structures (`three(...)`, `add(...)`, `empties(...)`).
2. `benchmarks/native/lru.c` (a NEW protected-directory file) must be the
   optimized C reference: the same algorithm as the retained
   `reference/lru` (hash map plus an intrusive recency list), the same
   argument stream (`lcg`), the same checksum (`mix`), the same
   `BENCH_REGIONS` driver as every other reference.

What the worker CAN do inside scope, and is doing, is the other half:
`benchmarks/bend/lru.bend` (the Bend driver) and the port of the minimum
`reference/lru` modules into `src/` with a `Metrics` layout whose flattened
constructor arity is below the native backend's 255 limit (the current
`reference/lru` cannot be compiled natively; `tests/runtime_defects/wide_arity.bend`
is the reduced case). Until the two protected changes are made, those rows
cannot be measured at all.

Proposed row table (sizes chosen to match the other structures' cost
profile; every operation gets small/medium/large and an empty-cache edge
case):

| operation | small | medium | large | edge |
|---|---|---|---|---|
| `add`, `get`, `peek`, `contains`, `remove` | 64 | 4096 | 262144 | 0 |
| `purge`, `resize`, `len` | 64 | 4096 | 262144 | 0 |
| `keys` | 64 | 4096 | 32768 | 0 |

## 2. `vertices`/`edges` measure list construction against a C fold (INFORMATIONAL)

Not a defect and NOT proposed as a change to the canonical rows: the
canonical `graph.vertices`/`graph.edges` rows must keep measuring the public
API, which returns a `List`.

Evidence: `benchmarks/native/graph.c` `fold_keys`/`fold_edges` produce the
observable enumeration by folding the tree with no allocation, while the
Bend API must build the list it returns. Measured (clean run,
`/tmp/bench_graph2.json`): `vertices/large` 30781 ns for 4096 vertices
(7.5 ns each) against 4240 ns (1.03 ns each); an isolated probe puts the
floor for "read a slot, cons it, fold the list" at 2.2 - 2.9 ns per element
against the reference's 1.18 ns, i.e. about 2.3x before any other cost.

If the operator wants a same-shape comparison, the supplemental form would
be a public indexed enumeration (`vertex_count` / `vertex_at`, proved equal
to `vertices`) measured against a C loop over the same enumeration, added as
EXTRA rows under `benchmarks/experiments/` with their own reference. The
canonical rows and their numbers would stay exactly as they are. This is
recorded for review only; nothing has been added.

## 3. `deque.new/medium` is the one unmeasurable row of the clean run

`deque.new medium` reports `A-B = 40000000ns (bend) / 15626000ns (reference)`,
just below the 50 ms Bend minimum, because `new` is so cheap that the
difference is dominated by the per-round build. Every other `new` row at the
same size measures. This is a calibration edge, not a defect: the row needs
a larger `count` cap for size-preserving constructors in
`benchmarks/workloads.py` (protected). Proposed: raise that row's `count`
from its current value to the `50000` used by the other `new` rows.

---

## Worker response to the operator review (2026-09-21, same day)

1. **The blocker was never the workload table.** `reference/lru` could not be
   compiled by the native backend at all: "an arity over 255". Diagnosed:
   the backend FLATTENS constructor fields, `Word(64n)` flattens to 64 slots,
   and `Counts{inserts, evictions, removals, hits, misses}` therefore needs
   320. Measured here: three `Word(64n)` fields compile, four do not; nesting
   them in another record or in a two-constructor wrapper does NOT help
   (flattening is recursive); a recursive container does.

2. **Solved inside the editable scope.** `src/lru/model.bend` keeps the five
   counters in a `List<&2, Word(64n)>` with positional accessors, so their
   64-bit values and wrap-around are unchanged; `src/lru/{wide,time,codec,
   cache}.bend` are copies of the snapshot's modules with only that import
   and the eleven `T.Counts{...}` sites changed. Verified natively: a
   capacity-2 cache after `add a, add b, add c` reports `len = 2` and
   `get "b" = 2`. `reference/lru` is untouched and still hash-pinned.

3. **Rows prepared** in `benchmarks/experiments/lru_workloads.py` as
   requested: selectors, per-operation growth classification (including
   `remove` as a restoring pair), the checksum each side folds, and the
   sizes, with the reasons.

4. **[REJECTED by the operator 2026-09-21 and SUPERSEDED by the 0006
   response below -- kept only as history.]** Still to come before those rows can run: `benchmarks/bend/lru.bend`
   (driver over the ported cache) and `benchmarks/native/lru.c`. The C twin
   will implement the SAME algorithm as the retained snapshot -- a
   String-keyed map plus a recency LIST of encoded keys with linear removal
   and append -- because that is what the snapshot does; an intrusive O(1)
   LRU would be a different algorithm. That difference is recorded in
   docs/C_EQUIVALENCE.md rather than hidden.

5. **Noted and not done:** the deque calibration change is not approved and
   has not been made; no existing C reference, threshold or canonical row has
   been touched; the graph enumeration idea stays an informational note.

---

## Worker response to the LRU-reference rejection (iteration 0006)

The rejected linear reference is quarantined
(`docs/archive/lru-rejected-linear-reference.c.txt`) and is not used or
presented as a baseline anywhere. The 18 pinned files are unchanged.

1. **New C reference** `benchmarks/native/lru.c`: open-addressing hash
   (linear probing, load <= 1/2, backward-shift deletion, buckets hold
   key + slot) plus an intrusive indexed doubly linked recency list with a
   free list: O(1) touch/detach/evict/remove, O(table) purge, resize evicts
   from the head. Keys are `uint32_t`; there is no key buffer, so the
   `key_of`/`memcpy` partial-initialisation defect cannot recur.
2. **New Bend implementation** `src/lru/fast.bend`, driven by
   `benchmarks/bend/lru.bend`: the retained semantics with the native `Map`
   kept for lookup (key -> slot) and the same intrusive doubly linked arena
   for recency; 64-bit times/metrics as U32 limbs instead of `Word(64n)`.
3. **Validation** `python3 tools/lru_diff.py [--quick]`: Bend driver vs C
   (benchmark flags) vs C (`-fsanitize=address,undefined
   -fno-sanitize-recover=all`), all region checksums, every selector, sizes
   0..257 (full run to 4096), counts 0..200 (full: 1500), two seeds, both
   region orders. Result: 1568 cases, 0 mismatches, no sanitizer report.
4. **Workload semantics audited and corrected** in
   `benchmarks/experiments/lru_workloads.py` (still NOT applied):
   * `purge` and `resize` are added to `SIZE_CHANGING_FULL`, so they are
     whole-round (`grow='reps'`) rows; the default `growth()` would have
     classified them size-preserving;
   * whole rounds alone are not enough (A runs 2k, B k operations, so A - B
     would be purges of an EMPTY cache): the measured purge is
     `purge + refill` of the full cache and the measured resize is
     `shrink to 1 + lcg % size, grow back, re-add exactly the evicted keys`,
     restoring pairs whose every call does real work; the empty/no-op cases
     are separate, explicitly labelled `edge-empty` rows (selectors 5, 6);
   * `new` constructs a cache of capacity `size` through the validating
     constructor and folds the constructed cache's capacity and length
     (capacity 0: the rejection code).
5. **Measured with the canonical machinery** (`python3 tools/lru_measure.py`
   imports `benchmarks/run.py` unchanged and calls its `build_all` and
   `measure` on the proposed rows; report
   `build/performance/lru_experiment.json`). All 40 rows verified. They are
   far over 2.5x for every keyed operation (e.g. `get` 96.82 ns vs 10.39 ns
   small, 784.38 ns vs 41.24 ns large; the full table with absolute times is
   in docs/C_EQUIVALENCE.md). Cause, measured in isolation
   (`benchmarks/experiments/map_get_floor.bend`): the native `Map.get` alone
   costs 41 ns at 64 keys, four times the whole C `get`, because it descends
   a persistent patricia trie and rebuilds the walked path. **With the
   native Map retained as directed, the keyed `lru.*` rows cannot meet the
   2.5x target against a hash-table reference.** This is reported for the
   operator's decision; nothing has been relaxed and the C reference has not
   been slowed.

## Worker notes, iteration 0008

1. **The indexed LRU is now proven** (`proofs/lru_fast.bend`; laws
   `lru_fast_*` in END_TO_END.bend). The proposal in section 1 is unchanged:
   the nine `lru.*` rows still need the operator to add them to the protected
   workload table. Re-measured today with `tools/lru_measure.py` (table in
   docs/C_EQUIVALENCE.md): keyed rows 4-185x, len 0.3x, new 2.1x, keys
   3.2-6.3x, purge / resize restoring pairs 40-77x. The keyed rows are
   bounded by the native crit-bit Map, as measured in isolation before.
2. **prefix_trie representation versus its pinned reference (DECISION NEEDED).**
   The operator's representation rule forbids linked-list storage merely to
   hold trie children. `src/prefix_trie.bend` still keeps each node's children
   as a first-child/next-sibling chain. The pinned C reference
   `benchmarks/native/prefix_trie.c` (protected) implements that SAME chain. So
   migrating the Bend trie to indexed children (for example a node arena whose
   children are a sorted `U32` block searched by character, as the graph's
   adjacency blocks are) would make the pinned reference a different
   algorithm, and the rows would compare unlike things. Proposal: when the
   Bend trie migrates, add a matching C reference
   (`benchmarks/native/prefix_trie_indexed.c`: node arena, per-node sorted
   child arrays, the same doubling policy) and point the `prefix_trie.*` rows
   at it, keeping the old file for provenance. No change has been made; the
   migration and its re-proof are the next representation item.
3. **Structural limits met in the 0008 triage** (not requests to relax
   anything, recorded so the operator can see why rows are still over):
   * `to_list`-style rows build and consume a `List<&2, T>`, measured at
     about 10.9 ns per cell on the Bend side (`tools/costmodel.py` `fresh`)
     against about 2 ns in the C arena. That bounds them near 5x whatever the
     structure's representation is.
   * `prefix_trie` edge-empty rows (50-110x): the driver spells a
     10-character `String` key (20 cells: `SCon` plus `Chr`) inside the timed
     loop on both sides; C writes 10 words to a stack buffer. Spelling the
     key costs about 66 ns on the Bend side, and dropping the unread tail in
     `contains` on an empty trie brings it to about 127 ns
     (`tools/dev/quick_bench.py`).
   * `balanced_search_tree` reads walk retained `&2` nodes (about 9 ns per
     node against about 1 ns in C). An arena red-black tree would move the
     reads to indexed `Base.Array` loads, which are at parity with C, but it
     means re-proving the whole tree.

## Worker notes, iteration 0011

1. **deque / queue are ring buffers now; supplemental C twins proposed.**
   `src/deque.bend` was a drifting window (pops moved `lo`, a push doubled the
   block whenever the window touched its end, so memory followed the lifetime
   number of pushes and the trace law carried `1 + 2(P + pushes) < 2^q`). It
   is now a true ring buffer: element j in slot `wrap(lo + j)`, growth (an
   in-order copy into a block twice as large, `lo = 0`) only when
   `len == cap`, unboxed `Array<T>` slots (no `Maybe` per slot), no block
   until the first push. Proofs re-established from scratch
   (`proofs/deque/{ring,state,grow,stepok,reads,pushes,steps,trace}.bend`,
   `proofs/queue/{steps,trace}.bend`); the only premise is on the PEAK size
   (`pushok`/`fits`: every push happens while the deque holds fewer than 2^q
   elements, q <= 31). The old sources/proofs are archived as
   `docs/archive/*drifting_window*`.

   The pinned `benchmarks/native/deque.c` / `queue.c` implement the old
   window. Proposal: add `benchmarks/experiments/deque_ring.c` and
   `benchmarks/experiments/queue_ring.c` (same driver contract, same ring
   algorithm, arena slots, `memcpy` in two pieces on growth, branch-free
   modular index) as the references of the `deque.*` / `queue.*` rows, and
   keep the old files for provenance. Verified: Bend, the ring twin and the
   pinned reference produce IDENTICAL checksums for every deque and queue
   selector at sizes 0, 64 and 4096 (the observable behaviour did not
   change). Until the operator decides, the gate keeps measuring against the
   pinned files, and BENCHMARKS.md reports those numbers; timings against
   the twins are in docs/C_EQUIVALENCE.md as supplemental evidence only.
2. **Driver structure affects clang's inlining (a harness-side finding on
   the Bend drivers only).** Every Bend def compiles to one `static inline` C
   function; clang inlines one only while it has a single caller. A step
   helper shared by two measured loops (for example `do_pb` in both the push
   loop and the push/pop pair loop) was compiled out of line in both, and the
   push row doubled (2.3 -> 4.8 ns). The Bend drivers now give every library
   operation one call site (merged loops with per-loop flags), and count
   lists with a tail loop (Base's `List.length` is not a tail recursion).
   The C references are untouched. Separately, the drivers parsed argv into
   a shared (`+`) `List<String>`; the runtime reference-counts EVERY node of
   a type that is shared anywhere in the program, so that one shared list
   made each cons of `to_list`/`range`/`prefix_entries` pay an extra
   reference-count cell (deque to_list 4.5x -> 1.6-2.4x once argv is parsed
   into scalars, `benchmarks/bend/common.bend` `Args`). Both are changes to
   the editable Bend drivers only; the measured operations, counts, value
   streams and checksums are unchanged (checksums verified equal).

## Proposal (iteration 0014): prefix_trie rows measure Base String construction

**Status: proposal only. No canonical file is changed. The pinned rows keep
being reported as they are.**

### Measured finding

Every `prefix_trie.*` row is dominated by building the 10-character key, not by
the trie. The key is a `Base` `String`, a cons list of `Chr`: ten characters are
twenty heap cells. The pinned `benchmarks/native/prefix_trie.c` builds the same
key with ten stores into a `uint32_t key[10]` stack array.

Evidence (tools/dev/qrows.py, ns per operation, best of three alternating runs;
the Bend variant is the driver with the `contains` call replaced by folding the
key into the checksum, so the trie does no work at all):

| what | Bend | C (complete operation) |
|---|---|---|
| `contains` edge-empty (empty trie) | 96.4 | 1.13 |
| key construction only, edge-empty | 99.6 | (C's whole op: 1.45) |
| `contains` small | 212.0 | 24.6 |
| key construction only, small | 87.3 | (C's whole op: 26.8) |
| 10-char key built and folded, no trie in the program (`benchmarks/experiments/key/keycost.bend`) | 30 ns/key | ~1 ns/key |

On the empty-trie rows the Bend program spends ~99 ns building and freeing a key
while the C program spends ~1.4 ns on the *entire* operation; the trie
contributes nothing to that row.

### Why this is not an implementation defect we can optimise away

* The objective requires String/Char keys for the trie, and the operator rule
  forbids reimplementing native String.
* Building the key is *input generation*, which the performance contract says
  must be "excluded from operation timings symmetrically". The pinned harness
  builds it inside the timed region, where it costs ~1 ns in C and ~30-100 ns
  in Bend, so the row does not compare the two tries.
* The avoidable part is already fixed in the driver (the variable `U32.shrn`
  shift, ~25 one-bit steps per character, is gone; checksums unchanged).

### Requested additive rows (for operator review)

`prefix_trie.<op>.prepared_keys` for insert / lookup / remove / contains /
prefix_entries / longest_prefix, small / medium / large / edge-empty: identical
workloads and identical checksums, but the `count` keys of the round are built
once into a prepared input (a Bend `List<String>` and the same C array of key
buffers) BEFORE the timed region on both sides, and the measured loop consumes
one prepared key per operation. The existing rows stay exactly as they are and
keep being reported.

## Addendum (iteration 0014): the two missing LRU coverage rows

The operator asked the supplemental LRU suite to cover "capacity/set_lifetime/
metrics and expiry" as well as the isolated destructive operations. Already
covered by the proposed rows: capacity (selector 9 `new` folds the constructed
cache's capacity and length, and the rejection code for capacity 0), metrics
(every round's drain folds the length and both halves of all five 64-bit
metrics on both sides) and the isolated destructive operations (selectors 10-12
are restoring pairs; the no-op cases are separate `edge-empty` rows).

Still to add - both drivers take an explicit timestamp per operation, so this is
deterministic and needs no wall clock:

* `lru.set_lifetime` (new selector 13): sets the cache lifetime to
  `1 + lcg % 1000` ms and folds the cache's length and capacity, so the call is
  observable. Small / medium / large / edge-empty.
* `lru.expiry` (new selector 14): with a lifetime L set once per round, adds key
  i at stamp s and reads it back at stamp `s + (lcg % 2L)`, so about half the
  reads are past the deadline; it folds the read result and, in the drain, the
  removals and misses metrics, which is where an expired read must show up.
  Small / medium / large / edge-empty.

Both rows would exercise `src/lru/fast.bend` paths the nine contract operations
do not: `set_lifetime` (the `ttl` flag and the retained `deadline_choose` test)
and the `Timed{v, dl}` slot form with its deadline comparison on every read.

## Iteration 0015: the LRU coverage rows are now IMPLEMENTED, not just proposed

**Status: still proposal only for the canonical table. No canonical file is
changed.** What changed in iteration 0015 is that the additive rows now exist as
running code in the two editable LRU drivers (`benchmarks/bend/lru.bend` and
`benchmarks/native/lru.c`, neither of which is one of the 18 pinned files), so
the operator can review measured rows instead of a description.

### New selectors (both drivers, append-only: selectors 0-12 are untouched)

| sel | row | what one measured step does |
|---|---|---|
| 13 | `lru.capacity` | `capacity(c)`; folds it |
| 14 | `lru.set_lifetime` | `set_lifetime(c, ns)` with `ns = lcg mod (size+1)`; folds `ns` and the length |
| 15 | `lru.metrics` | `metrics(c)`; folds all five 64-bit counters (ten U32 limbs) |
| 16 | `lru.expiry` | adds key `i` at stamp 0 with the round's 1 ms lifetime (deadline 1) and gets it back at stamp 2: the read finds it EXPIRED, drops it (a removal) and answers a miss. COMPOSITE (add + get), labelled as one. |
| 17 | `lru.remove_seq` | ISOLATED removal of the still-present key `(o+j) mod cap`; `count = size/2`, so region A is exactly one full sweep and region B its first half |
| 18 | `lru.purge_isolated` | ISOLATED purge: every region builds the SAME pool of `2 x (the ROW's count)` independent full caches, so the preparation cancels in A-B; A purges 2k of them and B k, and every measured purge empties a freshly prepared FULL cache |
| 19 | `lru.resize_isolated` | ISOLATED shrink over the same pool: cache j is resized to `1 + lcg mod cap`; every measured resize really evicts |

This answers the three open points of docs/OPERATOR_LRU_BENCHMARK_REVIEW.md:

1. *Isolated destructive rows on independent nonempty states.* Selectors 17, 18
   and 19 do exactly that. The C driver cannot see the row's `count` (the
   frozen `BENCH_REGIONS` macro only hands `round_fn` the REGION's count), so
   `benchmarks/native/lru.c` now expands `BENCH_MAIN` by hand with one extra
   line, `g_pool = a.count;`, before the regions run. That is the only reason
   the macro is not used verbatim; nothing else about the timing changes.
   The composite rows 10/11/12 are KEPT and stay labelled `remove+add`,
   `purge+refill`, `resize+back`. They are diagnostics, not isolated acceptance.
2. *capacity / set_lifetime / metrics / expiry.* Selectors 13-16, with
   small/medium/large and `edge-empty` rows. All thirteen public operations of
   `src/lru/fast.bend` (`new, len, capacity, set_lifetime, metrics, add, get,
   peek, contains, remove, purge, resize, keys`) now have their own row.
3. *Reviewable parity.* `python3 tools/lru_diff.py` now sweeps selectors 0-19
   (the pooled ones over a bounded size/count grid, because each of their
   regions builds `2 x count` whole caches). Bend, the optimized C build and an
   ASan+UBSan C build must agree on all three region checksums, in both region
   orders.

### Honest limitation of the pooled rows

Preparing a full cache costs more than purging or shrinking it, and the
preparation is paid in EVERY region. It therefore cancels in `A - B` but
inflates both terms, so `A - B` is a small difference of two large numbers and
these rows need long regions and modest sizes to stay above the harness's noise
floor. That is the unavoidable price of isolation, and it is why the composite
rows are kept next to them rather than replaced.

## Iteration 0015: measured floors of the stock Bend runtime

These are reproducible micro-measurements, added so that the per-row analysis in
docs/C_EQUIVALENCE.md rests on evidence rather than on assertion. They are
development measurements (`IO.now()` inside the program, milliseconds, one
sequential thread, shared machine), never acceptance evidence.

| what | program | Bend | optimized C doing the same |
|---|---|---|---|
| build + fold one 10-character `Base.String` key | `benchmarks/experiments/key/keycost.bend` | 36-40 ns | ~1-2 ns (ten stores into `uint32_t key[10]`) |
| one level of a data-dependent descent over a native indexed `Array<U32>` block | `benchmarks/experiments/bstarena/descent.bend` | 1.9 ns | (a dependent L1 chase, ~1 ns) |
| one level of the SAME descent over a SHARED algebraic tree | `benchmarks/experiments/bstarena/descent_adt.bend` | 13.2 ns | - |
| filling a fresh 262144-slot `Array<Maybe<U32>>` (what `dynamic_array.clear` does) | `dynamic_array.clear large` | 236 us | 15.3 us (`memset` of the same 2 MB) |

What follows from them:

* **A shared algebraic node costs ~7x an indexed block slot** to walk, because
  opening a shared constructor has to retain every field and release the ones
  the walk does not follow (`span_fade` / `term_drop` in the emitted C). This is
  why the array-backed structures meet the target and the two pointer-shaped
  ones (`balanced_search_tree`, `prefix_trie`) do not. It is ALSO why moving
  those two onto an indexed arena is worth doing on its own merits and is
  recorded as the next representation step - but the same numbers say it would
  take `balanced_search_tree.min/small` from ~39x to roughly 8-11x of a C walk
  that costs 1.0 ns, not to 2.5x.
* **A 10-character `String` key costs more than the whole C operation** on every
  `prefix_trie` row, which is what the `prepared_keys` proposal above is about.
* **Bend's block fill is ~15x `memset`**: the emitted `blk_new` writes one word
  at a time through the `u32a` device pointer type and is not vectorised. Every
  row whose work is a bulk fill (`dynamic_array.clear`) inherits that factor.

No canonical row, reference, threshold or workload is changed by any of this.

## Harness defect found in iteration 0015: the pinned queue/deque reference can exhaust its arena and ABORT the whole run

**Evidence.** `python benchmarks/run.py --report build/performance/report.json`
aborted after 90 of 408 rows with

```
reference run failed: arena exhausted (2147483664 of 2147483648)
```

on `queue.dequeue large` (size 262144). `benchmarks/run.py:181` raises
`SystemExit` when the reference process fails, so ONE reference that runs out
of arena discards the whole 408-row run; it is not recorded as a failed
measurement for that row.

**Why it happens, and why it is new.** `queue.dequeue` is measured as the
restoring pair enqueue+dequeue. `benchmarks/native/queue.c` (pinned) is the
DRIFTING-WINDOW queue: `lo` advances, the block doubles at the end, and the
arena is a bump allocator, so its memory grows with the LIFETIME number of
pushes, not with the element count. `src/queue.bend` has been a true RING
since iteration 0011 (operator review: docs/OPERATOR_RING_REFERENCE_REVIEW.md),
so its memory is bounded by the peak size and its `dequeue` measures 0.31x of
the reference. The calibration lengthens the batch until the BEND difference
exceeds 100 ms; the faster Bend is, the longer the batch, and the more the
reference allocates:

| run | count x reps | bend ns/op | outcome |
|---|---|---|---|
| iteration 0013 | 48,000,000 x 1 | 2.33 | 48 M pairs, arena survived |
| iteration 0015 | ~96,000,000 x 1 | 2.04-2.20 | arena exhausted at 2 GB, RUN ABORTED |

100 ms / 2.2 ns = 45.5 M operations, so the calibration sits exactly on the
boundary between 48 M (survives) and 96 M (dies): whether a 408-row run
completes is currently decided by measurement noise on one row. The same risk
applies to `deque.pop_front` / `deque.pop_back`.

**What this proposal asks for (operator decision).** Nothing has been changed:
`benchmarks/run.py`, `benchmarks/workloads.py` and `benchmarks/native/queue.c`
and `deque.c` are untouched. One of

1. record a reference process failure as `measurement="failed"` for that row
   (the treatment `Unmeasurable` already gets) instead of aborting the run --
   this is the smallest change and loses no evidence; or
2. raise the pinned `queue.c` / `deque.c` arena above 2 GB (they are
   `BENCH_MAIN(round_qu, 2048 MB)`); or
3. adopt the supplemental ring twins `benchmarks/experiments/{queue,deque}_ring.c`
   (checksum-identical to both the Bend driver and the pinned reference for
   every selector, see the iteration 0011 notes above) as the reference for
   these rows, which also removes the ring-versus-drifting-window algorithm
   divergence.

Until then a full run has to be retried until the calibration happens to land
on the low side, which is what iteration 0015 did.
