# Snapshot status — bend-collections

Private development snapshot, not a finished or fully verified release.

Progress: native-array ports for several collections, binary heap implementation
and ongoing heap invariant/trace proofs. The full <=2.5x C gate is NOT satisfied.

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
