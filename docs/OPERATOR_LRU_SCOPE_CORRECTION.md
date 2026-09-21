# Operator scope correction — 2026-09-21

Restart reason: worker inferred that src/lru/fast.bend is outside official scope
because LRU is absent from canonical workloads. This is incorrect. OBJECTIVE.md
explicitly says the listed operations are the MINIMUM, not permission to omit
public APIs, and that DSA includes reused LRU in these benchmarks.

Preserve all current work, including the validated indexed graph and DLL,
red-black-tree integration work and latest heap/queue/deque capacity changes.
DLL evidence /tmp/v_dll.json passed all12operations, trace, boundaries,
5differential histories and6mutations; source-matched snapshot6ce40ef was pushed
by the operator. No new DLL timing acceptance is claimed.

Native Map/indexed LRU remains mandatory. Its new runtime needs universal
refinement/trace proofs; retained old LRU proofs do not prove fast.bend. Its
native C comparison and every public operation remain required. A missing row
in the frozen minimum gate is a coverage gap, not a scope exemption. Keep the
18 pinned C/workload files unchanged. Continue implementing the LRU proof and
reviewable experimental suite within authorized files. Do not modify canonical
harness/workload pins yourself. Follow BENCHMARK_CHANGE_PROPOSAL and the operator's
existing notes about fair destructive-operation reset/setup; do not relabel
purge+refill or resize+refill as isolated purge/resize acceptance.

Continue ALL remaining work end-to-end, not just LRU. Preserve original
propositions, expose capacity premises, instantiate templates, self-audit all
public laws and correct the missing benchmark coverage before completion.
