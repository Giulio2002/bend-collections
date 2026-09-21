# Current milestone: indexed graph prototype and search proof

This development snapshot is NOT a finished or fully verified release.
Graph storage now uses indexed vertex slots and adjacency blocks. The 40-row
prototype benchmark has 25 rows within 2.5x C, 15 slow, zero unmeasurable.
References remain unchanged. Source changed after benchmarking; exact mismatches
are recorded in SNAPSHOT.json, so the report is historical evidence, not a
certification of this snapshot's speed. Old full-suite results below are also
historical and no longer certify this source.

The actual array-backed binary-search and locate proof module checked separately,
with 7 unsafe annotations reported from its dependency graph. Trust-boundary
review remains required. Full graph PROOF/END_TO_END migration is incomplete:
shift loops, adjacency updates, operation refinements and traces remain.
No whole-library correctness or performance acceptance is claimed.

---

# Snapshot status — bend-collections

Private development snapshot, not a finished or fully verified release.

Progress: native-array ports for several collections, binary heap implementation
and ongoing heap invariant/trace proofs. The full <=2.5x C gate is NOT satisfied.

## Full native benchmark — 2026-09-20 23:10 UTC

All 408 workload rows completed in 3592 seconds: **199 <=2.5x C, 200 too slow,
9 unmeasurable**. The performance gate fails. There are 0 mismatches among the
209 benchmark source hashes and this export (see SNAPSHOT.json). Reused LRU
performance rows are still absent; this report covers the twelve new structures.

| Structure | <=2.5x | Too slow | Unmeasurable |
|---|---:|---:|---:|
| dynamic_array | 30 | 10 | 0 |
| deque | 21 | 15 | 0 |
| queue | 12 | 12 | 0 |
| doubly_linked_list | 9 | 37 | 2 |
| binary_heap | 27 | 1 | 0 |
| balanced_search_tree | 11 | 33 | 0 |
| bitset | 27 | 15 | 2 |
| union_find | 16 | 7 | 1 |
| fenwick_tree | 20 | 4 | 0 |
| segment_tree | 17 | 10 | 1 |
| prefix_trie | 4 | 24 | 0 |
| graph | 5 | 32 | 3 |

Worst measured row: prefix_trie.contains on edge-empty, 120.57x. Imported
proof annotations and independent semantic audit remain separate outstanding
work. Earlier reports used different source/harness versions; passing-row count
differences are not a controlled before/after speedup claim. Raw samples,
checksums, source manifests and measurement details are in
`snapshot-evidence/performance-full.json`; failed measurements are not passes.

## Full validation milestone — 2026-09-20 22:10 UTC

`validation-full.json` records complete=true and no failures in 127.4 seconds:
all twelve structures pass runtime, differential, boundary, mutation and trace
checks; reused LRU checks also pass. The report contains 193 source hashes, with 0 mismatches against this export (listed in SNAPSHOT.json).
This is validator completion, not final performance or semantic acceptance.
Imported graphs still report unsafe annotations (1180 in reused LRU roots);
their provenance and soundness require independent audit.

`perf-binary-heap-latest.json` retains the more recent heap measurement.
The worker reported two pop rows above 2.5x (2.72x and 2.63x); the full
benchmark rerun is in progress. Earlier partial reports below are historical.

## Earlier milestone: heap integration validation

The targeted heap validator now passes runtime, differential/boundary tests,
trace-proof checking and all six semantic mutation rejections. Raw report:
`snapshot-evidence/validation-binary-heap.json`. It is a subset, so complete=false
is expected. Checker output contains 861 unsafe annotations across dependencies;
this is not an independent end-to-end proof/trust audit. Performance remains
separate: the earlier heap benchmark had 26/28 within 2.5x, one over and one
unmeasurable, and predates these latest proof/API edits.

## Retained benchmark evidence

These are historical targeted runs from this work session, NOT a fresh test of
this exact snapshot. Raw samples, environment and measured source hashes are
in `snapshot-evidence/`. Changes after each run are listed in
`SNAPSHOT.json`; do not combine these rows into a current full-suite pass rate.

| Report | <=2.5x C | Too slow | Unmeasurable |
|---|---:|---:|---:|
| perf-binary-heap.json | 26 | 1 | 1 |
| perf-da2.json | 27 | 9 | 4 |
| perf-dq3.json | 26 | 4 | 6 |
| perf-fen2.json | 20 | 4 | 0 |
| perf-qu.json | 14 | 5 | 5 |
| perf-seg.json | 17 | 11 | 0 |

Run `python3 benchmarks/run.py --report build/performance/report.json` and
`python3 automation/performance_gate.py` for fresh native evidence after installing
the pinned dependencies. C sources and harness are included. Some tree/trie C
references were found to traverse twice where Bend traverses once; these need
correction/review before final acceptance. Full proof closure and concrete
instances remain incomplete, and unsafe annotation trust boundaries need review.

## Follow-up validation evidence

The active worker's full validation run reported graph runtime, boundary,
differential and mutation tests passing, but overall complete=false:
DLL driver handle formatting expects Nat instead of the new U32, and the
graph trace proof still expects the old state shape. This evidence is from
the ongoing workspace; source differences against this snapshot are explicitly
listed in SNAPSHOT.json. It does not certify this exact snapshot or complete proofs.
