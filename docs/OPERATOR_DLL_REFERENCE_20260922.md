# Deque and queue C reference repair (2026-09-22)

The operator requested a doubly linked-list deque in C and Bend, then asked to
repair the C benchmark and inspect similar cases. `benchmarks/native/deque.c`
and `queue.c` now share `dll_deque.h`: an indexed doubly linked list with a
reusable free-slot chain, one geometrically grown allocation, and actual release
at the end of each round. Queue is the FIFO specialization of this deque.

The old sliding-window references are preserved under benchmarks/reference-history.
Their storage grew with lifetime insertions, even for fixed occupancy, eventually
exhausting a 2 GB bump arena. Raising that arena limit was not the repair. The new
references do not use it for nodes. The common harness's unused compatibility
arena is 16 bytes. Node storage is allocated and freed inside the original rounds.
A to_list result is materialized in temporary linked cells and freed per call.

No changes were made to common.h, workloads.py, run.py, operation selectors, LCG,
checksum definitions, the restoring pairs, or timing thresholds. C uses the normal
-O3 -march=native build. The independent C references are not padded to mimic Bend
allocation overhead; C packs node fields in one allocation while the current Bend
DLL uses parallel arrays.

## Similar cases

* Queue had exactly the same drifting-window/bump-arena bug and is repaired here.
* Public doubly_linked_list.c deliberately has monotonic stable handle IDs and no
  reuse. It has similar lifetime growth, but changing slot reuse without generations
  would let stale handles alias new values. It is NOT silently changed here. The
  corresponding Bend worker must preserve stale-handle safety when adding reuse.
* LRU already has a free-slot chain; it does not have the same per-removal problem.
  Its hash-table rebuild and allocation behavior still need sustained-workload tests;
  this inspection is not a general memory certificate for all structures.

## Validation and measurement boundary

benchmarks/check_dll_deque.c checks complete values and bidirectional links against
an independent array model over 200,000 operations, then runs 10,000,000 FIFO
restoring pairs at live occupancy 262,144. It asserts used <= 262,145 and capacity
<=524,288 throughout. ASan/UBSan passed. Node storage plateaued at 6,291,456 bytes;
this is allocated node storage, not a process RSS measurement.

Reproduce:

    cc -O1 -g -fsanitize=address,undefined -std=c11 benchmarks/check_dll_deque.c -o /tmp/check-dll
    /tmp/check-dll
    python3 benchmarks/operator_deque_bench.py

The diagnostic runner imports the unchanged canonical calibration/measurement
functions, takes the unchanged original rows and seeds, and preserves raw samples,
checksums, environment and source hashes. It measures all deque and queue rows.
Failures remain failures; no timing floor or clamping is added.

IMPORTANT: the preserved Bend deque is STILL A RING. Its DLL migration was paused
mid-implementation. These new C-vs-Bend results are diagnostic only, not matching-
algorithm acceptance, and cannot replace the old full-suite report. Once the Bend
DLL adapter and proofs are complete, rerun this exact reference/workload suite.
All latest snapshot proofs are work in progress; this repair does not prove them.

The 36 small-selector/order comparisons against the archived C programs also matched all three region checksums. These finite checks supplement the full-content differential test; checksum equality alone is not a proof of correctness.
