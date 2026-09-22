# Manual optimization pass, 2026-09-22

Union-find has been removed from implementation, C reference, test drivers,
proofs, inventory, workload table and performance requirements. Historical
reports may mention previous scope. No auto-implementer was restarted.

Arena DLL public operations now bypass the generic Op/Obs trace dispatcher.
The specialized paths retain generation validation and existing errors, slot
recycling and generation exhaustion behavior. `DLL_DIRECT_PROOF.bend` proves
get/set/next/prev/relative insert/remove equivalence to the old trace route for
U32 and String; length/list equivalence is checked for U32. This does not close
the outstanding full arena invariant/trace proof obligations. Public-path
oracle testing passed 41 histories / 1,766 operations including stale handles.

Red-black min/max traverse the extreme branch with tail calls. The existing
query theorem module has been updated and checks against the independent
in-order specification. Differential testing passed 45 histories / 2,323 ops.

Six alternating runs with matching checksums measured arena get at 15 ns
before and 2 ns after, C 1.303 ns. Tree min: 51.167 to 50.667 ns (effectively
unchanged); max: 56.667 to 53 ns. The tree remains far above the target.

An unrolled LRU limb-conversion experiment passed functional equivalence but
failed stock Bend compilation with an arity-over-255 error. It was reverted.
Retained C reference sources are byte-identical to the preceding publication.

Quick mode now attempts up to three valid samples per operation, alternating
region order; it retains the 60-second global budget. Additional-sample
timeouts retain already valid estimates with a note. It does not replace the
full calibrated acceptance gate. RNG seeds are pinned so removing a collection
does not change unrelated workloads. Fingerprints include workloads and seeds.

Final sweep: 33.691 seconds, 115 operations, 75 estimates <=2.5x, 35 above,
4 timeouts, 1 low-resolution row. See BENCHMARKS.md and raw evidence. These are
provisional results; no overall performance or formal-verification completion
is claimed. LRU, tree, stack-list traversal and other slow rows remain work.
