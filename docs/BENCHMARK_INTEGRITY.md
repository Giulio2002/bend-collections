USER BENCHMARK INTEGRITY CORRECTION — 2026-09-21
The user explicitly rejected slowing the C reference to mimic Bend overhead as cheating.
The graph C reference has been restored byte-for-byte to the version measured in the
published 408-row report. The analogous extra output-list allocation was removed
from the in-progress doubly-linked-list C reference while retaining its indexed arena.
Unrelated implementation, proofs, and worker session were preserved.

The target remains <=2.5x genuinely optimized C. Improve Bend, its representation,
and generated code. Never make C slower, add dummy allocations/work/barriers, remove
optimizations, change timing boundaries/counts/checksums, drop hard workloads, or
reinterpret an invalid measurement as a pass to improve the ratio. No FFI or custom
compiler. No changes that weaken proofs, omit runtime bridges, or narrow the goal.

Existing C references, common headers, timing runner and workload definitions are
now mechanically protected. The optimized graph fold is intentional and MUST remain.
Do not route around these files with replacement references or alternate timing paths.
If a genuine harness defect or new LRU coverage requires a change, write a concrete
proposal with evidence in docs/BENCHMARK_CHANGE_PROPOSAL.md, leave canonical files
unchanged, and continue implementation/proofs while the operator reviews it. An
unfavorable ratio is not a harness defect. New references must be optimized C and
reviewed before acceptance. Never weaken a baseline silently.

The ~10.6x graph.vertices result from the slowed reference is REJECTED. The retained
original measurement was ~28.26x (150 us Bend / 5.31 us C). Correct documentation
and keep experimental reports explicitly disqualified from acceptance.

Continue the ENTIRE remaining objective, not just a small checkpoint: all remaining
representation migrations, actual refinement/invariant/trace proofs, honest native
benchmarks including LRU, every existing workload <=2.5x, final independent audit.
Self-audit the generated C, reference provenance and actual operation counts. Report
Bend and C absolute timings alongside every claimed ratio improvement.
