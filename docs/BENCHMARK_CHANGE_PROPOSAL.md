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
