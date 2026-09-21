USER REQUIREMENT FOR EVERY DATA STRUCTURE — 2026-09-21
For ALL data structures, not just graph, implement the equivalent of genuinely
optimized C or the closest efficient stock-Bend representation. This extends the
graph direction and supplements every earlier assignment. Preserve graph priority
and all sound existing work; complete the entire library afterward.

Read the optimized C implementation and trace its algorithm, storage layout,
ownership, indexing, updates, traversal and output paths. Reproduce those choices
in Bend where supported; do not choose a slower representation just for easy proofs.
Use native block-lowered arrays and machine words in hot paths, deliberate affine
ownership, and appropriate fixed records. Avoid unnecessary boxing, copying,
unary Nat conversions, intermediate lists, persistent maps where indexed slots
suffice, or excessive helper transitions. Linked links are allowed when inherent
in the algorithm, e.g. prev/next indices for a doubly linked list. The balanced
search tree remains a genuine red-black tree; represent its nodes efficiently.
Native Map/Set/stack exclusions and the callback/concurrency exclusions remain.
Respect the retained native-Map LRU requirement; document unavoidable differences.
No FFI, custom compiler, patched generated C, weakened laws or restricted domains.

For each structure maintain docs/C_EQUIVALENCE.md with: C source and algorithm;
Bend representation; generated-C load/store/allocation/ownership evidence; any
remaining discrepancy and why; actual runtime-connected laws; absolute Bend/C
measurements and all failed rows. Distinguish the Base logical tree model from
native Array memory-block lowering. Stock 2.0.16 probe has established direct
indexed Array<U32> loads/stores; validate lowering for the actual element layout.

All existing pinned C references/timing/workloads remain unchanged. Do not make
C imitate Bend overhead. Supplemental genuinely optimized C twins for a new
algorithm may be proposed for operator review, with original results retained.
A reference slowdown is never implementation progress. Target <=2.5x C on every
required workload, including LRU, with no hidden conversions outside the timer.
Finish implementation + proofs + tests + native measurements + self-audit against
the independent auditor, keeping partial checkpoints inside ongoing work.
