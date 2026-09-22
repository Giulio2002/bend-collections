# Queue facades, 2026-09-22

LifoQueue and SimpleQueue expose put/get/qsize over the existing stack and FIFO
queue. PriorityQueue exposes them over the packed-array binary min-heap with
an explicit comparator. No synchronization or Python runtime compatibility is
claimed. Underlying errors and Data element restrictions are unchanged.

Bend benchmark drivers import these public modules. C drivers include their
same-algorithm references; includes reuse code, they do not invoke external
code from Bend. Workload selectors, RNG and restoring-pair semantics are
inherited unchanged. `get` timing includes its restoring insertion, on both
sides. The inventory and performance contract include all exported operations.

`python3 tools/check_queue_facades.py` runs 20 randomized histories of 400
operations per facade against independent Python models (24,000 operations).
Build the three `tests/<name>/main.bend` executables to `build/test-<name>` first.

`bend QUEUE_ADAPTER_PROOF.bend` checks definition-level delegation of put/get/
qsize for U32. This is deliberately a narrow component claim. Heap invariant
proofs and whole-library proof completion are separate obligations.
