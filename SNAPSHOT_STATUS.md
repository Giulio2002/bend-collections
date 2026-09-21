## Latest: indexed graph add_edge and add_vertex refinements

Independent exported-snapshot checks of proofs/graph/addedge.bend and
proofs/graph/addv3.bend pass, each reporting 94 unsafe annotations. Vertex
insertion covers all six runtime branches, including both table doublings.
Raw output is in snapshot-evidence/graph-add-{edge,vertex}-check.log.
The reported imported/generic trust boundary is still an audit obligation.
Vertex removal, whole-trace integration, DLL/new-LRU proofs and native speed
targets remain unfinished. No whole-library formal acceptance is claimed.

## Latest: indexed graph remove_edge refinement

Independent exported-snapshot check of proofs/graph/rmedge.bend passes with
94 unsafe annotations reported. The final so_remove_edge theorem connects the
actual indexed runtime to the specification, preserves the representation
invariant and does not grow the tracked measure. Raw checker output is in
snapshot-evidence/graph-remove-edge-check.log. No explicit unsafe/assume/postulate
or placeholder marker was found in the nine newly added graph proof modules;
this does NOT discharge the reported imported/generic trust boundary. Its
review remains mandatory, and this snapshot is not fully verified acceptance.

Add-edge, vertex update and whole-trace integration remain incomplete, as do
DLL/new-LRU proof migration and performance targets. No new timing result is
claimed for this proof-only milestone.

## Latest: indexed graph enumeration refinement

Independent checks of `proofs/graph/nbrs.bend` and `proofs/graph/edges.bend`
pass on this exported snapshot, each reporting 15 unsafe annotations. These
modules connect neighbors, vertices and edges enumeration to their abstract
models under representation invariants. Raw checker output is in
`snapshot-evidence/graph-enumeration-*-check.log`. The imported unsafe boundary
still requires review. This is not whole-graph or whole-library acceptance.

Graph updates and trace composition, indexed DLL proofs and the new LRU proof
remain unfinished. These enumeration APIs currently return lists; permission to
introduce efficient public array/view results does not mean that migration is
already implemented. Historical benchmark results below are not new performance
measurements and do not certify this source revision.

Independent exported-snapshot rerun: constructor mismatches 0; eight seeds x 3000 steps, all zero mismatches. Checker reports 52 imported unsafe annotations; trust-boundary review remains required. Raw output: snapshot-evidence/lru-fast-snapshot-differential.log.

## Latest: redesigned native-Map LRU runtime (proof incomplete)

The new runtime combines native Map lookup with an indexed doubly linked recency
arena and native-array counters. The C reference uses efficient open addressing
and intrusive indexed links; the rejected linear-recency C baseline is archived
only and is not an acceptance reference. Three recorded quick differential runs
report 1568 cases / zero mismatches, including sanitizer-enabled C. New behavioral
checks compare to the retained LRU, including expiry and maximum-capacity behavior.
The new runtime refinement proof remains unproved; the retained LRU proof does
not automatically cover this port. Graph/DLL proof migration also remains open.

The 40-row LRU performance report is EXPERIMENTAL, not canonical acceptance.
Keyed operations remain far above 2.5x C (get 9–19x, add 13–31x, contains up to
172x in this run). Purge/resize rows include refills and cannot establish isolated
operation performance. Correct destructive A/B workload design remains under
operator review. Existing canonical rows/references are unchanged. The report
predates subsequent source changes; mismatches are listed in SNAPSHOT.json.

## Latest: first indexed graph public operation refinement

`proofs/graph/ops.bend` now proves `has_vertex_ok` by connecting the actual
binary search to the specification under the representation invariant.
Independent check passed with 15 unsafe annotations reported in its imports;
that trust boundary still needs review. Shift, state and window proof modules
are included. Remaining graph operation/trace proofs and DLL proof migration
are unfinished. Historical benchmark/validation reports do not certify this
new snapshot; source differences are recorded in SNAPSHOT.json.

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
