# Application-owned list membership

These workloads compare `IntrusiveDoublyLinkedList`, the existing public
`DList` API, a diagnostic using its shared storage without the generation
facade, and plain indexed C. They answer two application questions:

- What does it cost to move an existing entity between groups by identity?
- Can a prewarmed working set serve repeated transient-object pulses without
  allocating nodes, membership wrappers or temporary runtime objects?

`DList` already provides O(1) known-handle removal and recycles arena slots.
Both Bend implementations recorded zero `heap_alloc` calls after warmup.
The intrusive API supplies application-owned membership, stable identity across
roots, and access to existing link fields. The checked `DList` API additionally
maintains ownership and generation validation, a tail and a count. These are
different contracts; a faster unchecked membership representation does not
replace those guarantees.

## Reproduce

From the repository root, with Bend 2.0.25, clang, Node.js and Python 3.10+:

```sh
python3 benchmarks/intrusive.py --bend bend --cc clang
```

This rebuilds all candidates, checks their outputs, measures working sets of
32, 1,024 and 65,536 entities, and writes `build/intrusive-bench/report.json`.
Use `--sizes 1024 --samples 10 --min-ms 10 --seed 1` to select a smaller sweep.
`--check-only` runs the correctness and allocator controls without the timing
sweep; `tools/check_intrusive.py` includes that mode in the focused gate.
The runner bounds sizes to the reserved storage model. The Bend entry points
are benchmark kernels with trusted arguments, not public input validators.

## Work definitions

**Transfer.** Start with `size` entities in root 0. Each step chooses an
existing identity from the same deterministic LCG stream, removes it from its
current root, and prepends it to the other root. The roots retain changing
orders: this is not an immediately cancelled move-out-and-back pair. The
payload stays in application storage. One unit is one remove plus one prepend.
The selection uses bits above the lowest eight LCG bits to avoid a trivial
low-bit cycle at power-of-two working-set sizes.

The intrusive variant uses the entity's own next/prev fields. The `DList`
variant stores the same external entity IDs and uses direct `remove` and
`push_front`, updating its external ID-to-handle map after each move. It does
not search for a value, use the general operation dispatcher or bypass handle
checks. Both of its arenas are prewarmed to the entire working-set size; neither
needs growth during a measured transfer. Each checksum covers both final list
orders and every entity's identity and payload.

**Pulses.** Precreate `size` entities and run one full warmup pulse. Every
measured pulse takes the entire working set from the pool, replaces every
payload, prepends each node, processes nodes by their saved identities in
creation order, removes them and returns them to the pool. One unit is this
complete lifecycle for one node; a pulse contains `size` units. The work
includes scratch-ID writes, payload reads/writes and observable processing
checksums. It exercises known-node removal away from the head.

Both variants use the same application-owned entity pool, payload storage and
issued-ID scratch space. The pool is supplied by this contribution in both
cases; this comparison isolates their membership representations. The `DList`
arena also reuses its slots, and gets a complete warmup pulse before timing.
Factory counts must remain exactly `size`; the final pool order, pool count,
empty active membership, all processed payloads and all final payloads feed
the checked output. Payload initialization is the application's explicit job,
not an implicit effect of returning a node to the pool.

## Measurement and validation

- Runtime command-line inputs select size, count and seed; the compiler cannot
  constant-fold a fixed workload. Every output is checked against an independent
  Python `OrderedDict`/stack model without intrusive links or DList handles.
- 18 boundary/seed cases (sizes 1, 3 and 32; seeds 0, 1 and `UINT32_MAX`;
  both workloads) run against all three Bend variants on C/JS and plain C:
  126 output comparisons.
  The full timing runs check their actual larger inputs against the same model.
- A narrow emitted-C hook brackets the unique `churn` function. It fails closed
  if the compiler changes that function's expected shape. Setup, arena growth,
  prewarm, command-line parsing, output hashing and destruction are outside the
  interval. The processing checksum inside each pulse remains timed.
- **Timing and allocation are separate builds.** Timing binaries contain only
  monotonic-clock boundaries, with no allocation counter. Allocation binaries
  count every Bend `heap_alloc` request inside the same region, including
  temporary tuples/closures and allocator free-list reuse. This measures neither
  OS `malloc` calls nor peak memory. Six positive controls add one forced
  request each and must report baseline + 1.
- The batch grows until the fastest candidate's calibration reaches 10 ms.
  Each candidate gets a discarded sample, then ten measured samples in
  rotating execution orders. An independent repeat of the exact same intrusive
  executable occupies another position in each round as an A/A control.
  Five cyclic orders give every label every position twice. The report flags
  A/A median drift above 10%; it is disclosed, never corrected away. All candidates receive identical work counts and
  seeds. Reported times are direct hot-loop durations; there is no subtraction,
  clamping, per-candidate work scaling or inferred operation cost.
- Native runs use one worker and clang `-O3`. The host is shared, without CPU
  affinity or frequency control. Medians describe this machine/run; the raw
  JSON also retains every sample, minima/maxima, batch sizes, checksums,
  toolchain identity and source hashes. There is no machine-dependent speed
  threshold in the correctness gate.

## Generation-layer diagnostic

The `storage` candidate calls the existing internal `dlist_storage` operations
with slot reuse, using the same application and workload. It omits the outer
generation array, generation validation/increment and generation entries in
the external handle map. It retains bounds, owner and live-slot checks, cached
tail/count, three membership arenas and the ID-to-slot map. It discards a
membership handle immediately after removal; no stale handle escapes and no
generation-wrap policy is needed for this restricted trace.

This is a diagnostic, not a proposed public unchecked DList API. Its difference
from the public DList includes generation storage, handle-map traffic and
compiler specialization, so it is not a pure measurement of one comparison
instruction. Its difference from intrusive still includes owning arena and
metadata work. The benchmark does not establish an equal-safety speedup or
attribute the entire difference to generation validation.

## Live memory

Separate memory builds account for each `heap_alloc` / `heap_free` size class,
from program start. At the churn boundary they record live bytes, then the
maximum live bytes during churn and the live bytes at exit. This includes
reserved, prewarmed membership arenas even when their slots are empty. The
runtime's size classes count corpus words; the hook converts these to bytes
and fails if its expected runtime shape changes or accounting becomes negative.
Six positive controls allocate and free an extra 8,192-byte block inside churn:
entry/exit bytes must match and the peak must increase by the expected amount.

These are **live Bend allocator-block bytes**, including size-class rounding,
not RSS, stack usage, OS malloc, free-list reserves or total process memory.
All candidates have the same external eight-field-per-entity array, including
fields one representation may leave unused. Thus the measurements describe
this reserved layout; they are not minimum bytes per entity. Root metadata can
be specialized into machine registers/stack and is outside this heap metric.

## Recorded results

The table below is generated from the committed raw run; method, values and
provenance travel together. Times are direct hot-loop medians, without
subtraction or a performance pass/fail threshold.

Recorded 2026-09-24 on AMD EPYC 9V74 80-Core Processor, Linux x86_64, Bend 2.0.25, clang 18.1.3. Ten samples per label, one worker. Times are median nanoseconds per transfer or complete pooled node lifecycle.

| Workload | Entities | Intrusive (ns) | Public DList (ns) | Storage diagnostic (ns) | C (ns) | DList / intrusive |
|---|---:|---:|---:|---:|---:|---:|
| Transfer | 32 | 5.59 | 50.67 | 41.72 | 3.44 | 9.06× |
| Transfer | 1,024 | 5.76 | 57.80 | 48.92 | 3.29 | 10.04× |
| Transfer | 65,536 | 9.16 | 105.23 | 86.60 | 6.10 | 11.49× |
| Pooled lifecycle | 32 | 4.53 | 15.75 | 13.66 | 3.95 | 3.48× |
| Pooled lifecycle | 1,024 | 4.71 | 16.82 | 13.21 | 4.16 | 3.57× |
| Pooled lifecycle | 65,536 | 4.67 | 16.78 | 13.38 | 4.34 | 3.60× |

All outputs match the oracle. Every warmed Bend candidate records zero `heap_alloc` calls across the full calibrated batches. No post-warmup factory calls occur. The A/A median difference is at most 2.4% across these rows.

Live bytes at churn entry, exit and hot-loop peak are equal within every row:

| Workload | Entities | Intrusive (bytes) | Public DList (bytes) | Storage diagnostic (bytes) |
|---|---:|---:|---:|---:|
| Transfer | 32 | 2,048 | 3,840 | 3,584 |
| Transfer | 1,024 | 65,536 | 122,880 | 114,688 |
| Transfer | 65,536 | 4,194,304 | 7,864,320 | 7,340,032 |
| Pooled lifecycle | 32 | 2,048 | 2,944 | 2,816 |
| Pooled lifecycle | 1,024 | 65,536 | 94,208 | 90,112 |
| Pooled lifecycle | 65,536 | 4,194,304 | 6,029,312 | 5,767,168 |

The common external entity array is included. Transfers prewarm two arenas; pulses prewarm one. These totals describe the measured representation, not a minimum object size or total process memory.

[Raw samples, A/A results, checksums, memory controls and source hashes](results/intrusive-linux-x86_64-2.0.25.json).

Results describe trusted IDs, primitive-array storage, these payloads and the
recorded compiler. The C reference uses intrusive links without DList's safety
checks. Arbitrary adapters, boxed payloads, allocation in callbacks, pool/arena
growth, generation exhaustion, concurrent mutation, JS performance and macOS
hardware require their own measurements. No GPU or parallel speedup is claimed.

## Sources and runnable examples

| Purpose | Files |
|---|---|
| Nominal identity and separate root reader/writer | `tests/intrusive_doubly_linked_list/example.bend` |
| Scheduler/render associations with preserved payloads | `tests/intrusive_doubly_linked_list/scheduler.bend` |
| Four entities, three pulses, twelve resets/reuses | `tests/intrusive_doubly_linked_list/pooled_pulses.bend` |
| Shared entity storage and pool | `benchmarks/bend/intrusive_support.bend` |
| Direct public DList handle adapter | `benchmarks/bend/intrusive_dlist_support.bend` |
| Generation-free diagnostic | `benchmarks/bend/intrusive_storage_support.bend`, `intrusive_{transfer,pulses}_storage.bend` |
| Transfer candidates | `benchmarks/bend/intrusive_transfer.bend`, `intrusive_transfer_dlist.bend` |
| Pulse candidates | `benchmarks/bend/intrusive_pulses.bend`, `intrusive_pulses_dlist.bend` |
| Same-work C reference | `benchmarks/native/intrusive_workloads.c` |
| Oracle, build, calibration and sampling | `benchmarks/intrusive.py` |
| Shared emitted-code instrumentation | `tools/intrusive_measurement.py` |

The aggregate `BENCHMARK.md` belongs to the existing operation benchmark and
its own recorded machine. This workload report keeps its method, inputs and
Linux results together rather than mixing unlike measurements into that table.
