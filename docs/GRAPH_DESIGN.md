USER GRAPH IMPLEMENTATION DIRECTION — 2026-09-21
The user explicitly chose indexed vertex storage plus adjacency blocks and asked
for the equivalent of a genuinely optimized C implementation, written in Bend.
Prioritize this graph implementation now; preserve unfinished DLL work and all
other completed implementation/proofs. Continue the whole remaining objective.

CRITICAL VERIFIED CORRECTION: Base.Array's tree-shaped definition is its logical
model, NOT the native C layout. Stock Bend 2.0.16 lowers Array<U32> to indexed
memory blocks. The operator compiled control/array-lowering-probe/probe.bend with
stock /Users/monkeair/.bend/bin/bend -o probe.c and cc -O3; it prints 42.
Generated C contains blk_new, blk_at, and direct blk_read/blk_write (no tree descent
for get/set). The evidence is at /Users/monkeair/work/dsa-performance/control/array-lowering-probe/.
Read the generated C. Do NOT repeat claims that native Base.Array indexing is
O(log capacity) merely from base.bend; distinguish checker model, native lowering,
construction/growth, element boxing and ownership. Correct misleading library docs.

Use optimized C-style indexed vertex slots and adjacency blocks in pure stock Bend:
- Prefer packed Array<U32> fields / suitable fixed records, checking actual C
  lowering before choosing AoS versus SoA. No cons-cell arrays, foreign algorithms,
  compiler forks, hand-edited generated C, or parallel benchmarking.
- Use machine-sized IDs/indices and cached lengths/capacities in hot loops;
  preserve full external U32 vertex-ID support with a proper ID-to-slot mapping.
  Do not assume only benchmark-dense IDs or reserve an existing legal ID silently.
- Preserve directed/undirected semantics, sorted observable enumeration, duplicate
  edges, self-loop and missing-vertex errors, and unchanged state on failures.
- Design efficient adjacency updates/traversal and vertex deletion; assess reverse
  adjacency against its cost. Prevent whole-graph cloning through affine ownership.
- Keep input/output paths efficient. Remove intermediate list materialization
  where the public contract permits; prove equivalent observable sequences and
  full runtime refinement rather than changing the specification to fit code.
- Build a small end-to-end graph prototype, inspect emitted C and test real graph
  operations against the unchanged optimized baseline before expanding the proof
  development. No claim of speed from line counts or theoretical layout alone.

REFERENCE INTEGRITY REQUIREMENTS STILL APPLY. All 18 pinned files remain frozen.
The existing optimized C reference is NOT to be slowed or replaced to improve ratios.
If the new algorithm needs its own C twin for same-algorithm measurement, implement
an independently optimized supplemental C reference under benchmarks/experiments/,
record checksums and absolute timings, and submit docs/BENCHMARK_CHANGE_PROPOSAL.md
for operator review before it can affect acceptance. Retain measurements against
the original baseline; never count a worse reference as a Bend speedup.

Prove slot validity, ID mapping, adjacency contents, undirected symmetry, absence
of stale edges on deletion, error-state preservation, and all public operation/trace
refinements. Keep existing independent specs and laws. Complete all remaining
structures and benchmarks after graph; do not stop at a prototype or checkpoint.
