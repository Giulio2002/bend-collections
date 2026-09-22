# Sentinel migration — incomplete

User requested conventional doubly linked nodes, a sentinel and stored length, with no indexed pool scheme, in both Bend and C.

## Implemented

`benchmarks/native/sentinel_list.h`: circular sentinel, stored size, malloc per inserted node and free on removal. Raw node pointers require live-membership preconditions and become invalid on removal. Initialized lists cannot be moved by struct copy because their sentinel address is stable.

C deque and queue adapters use this core. 100,000 randomized arbitrary-position insert/remove operations pass independent sequence checks, forward/backward invariants and allocation accounting (51,270 allocations, 51,270 frees), under AddressSanitizer and UndefinedBehaviorSanitizer. 240 benchmark input combinations preserve prior deque/queue checksums. These are tests, not formal proofs or performance acceptance measurements.

## Pending decision / work

Stock Bend 2.0.16 exposes affine arrays but no mutable node-reference primitive for a circular owning graph. User was asked whether to investigate a provable language extension or retain stock Bend with simple indexed sentinel links. Do not silently pick the latter: user explicitly rejected clever storage schemes.

The Bend code is still the prior indexed implementation. Its partial proofs do not prove this C core. The public DLL C benchmark is still the prior generational implementation; its safe stale-handle contract also differs from raw-pointer lifetime preconditions. Do not report full DLL migration, benchmark parity or formal completion.

Original C indexed references are archived in benchmarks/reference-history. No published benchmark acceptance evidence was overwritten. DSA worker remains stopped.

## Correction after capability experiment

The earlier blanket no-shared-node-reference claim was too strong: Base Chan can represent shared mutable node identity via sequential IO. A native circular-list prototype passes; see experiments/node-references/README.md. This is not an ordinary pointer DLL: inspected channel runtime uses indexed generation-tagged storage. It provides neither production performance evidence nor formal proofs. No representation choice is presumed approved by this experiment.
