# TreeMap implementation and benchmark evidence

Production module: `src/balanced_search_tree.bend`. Stock Bend 2.0.16, native C.
No FFI, compiler patches, or modified generated C. Optimized C reference unchanged.

92,544 operations across 300 histories pass, with structural/storage checks after
every operation; capacity rejection and free-slot reuse also pass. String keys
and custom Data payloads pass. Three compiled mutants are rejected by both tests
and the component proof gate. Sixteen component laws pass; universal indexed
refinement and full red-black/iterator/view preservation proofs remain open.
Existing Data-array and retained recursive-tree proof gates pass.

23/33 calibrated benchmark rows are within 2.5x, 10 are too slow, none unresolved
in the final sweep. This is **not performance acceptance**. First sweep is also
retained, including two noisy unresolved rows. Both sides use streaming folds
for range/iteration. Constructor rows call the real Bend constructor: allocating
the initial two buffers is included. The size denotes surrounding harness state,
not a nonempty newly constructed map. The unchanged C empty-tree constructor is
cheaper. No constructor row is replaced by a literal result in the final sweep.

| Operation | 64 | 4,096 | 131,072 |
|---|---:|---:|---:|
| tree_map.insert | 1.547x | 1.126x | 0.924x |
| tree_map.remove | 3.766x | 2.360x | 1.772x |
| tree_map.lookup | 1.982x | 1.619x | 1.368x |
| tree_map.contains | 1.660x | 1.557x | 1.510x |
| tree_map.min | 0.824x | 0.344x | 0.219x |
| tree_map.max | 0.825x | 0.534x | 0.237x |
| tree_map.lower_bound | 1.917x | 1.665x | 1.450x |
| tree_map.range | 6.688x | 16.687x | 15.600x |
| tree_map.iterate | 23.079x | 26.133x | 12.349x |
| tree_map.length | 0.351x | 0.348x | 0.350x |
| tree_map.new | 5.275x | 5.248x | 5.166x |

Raw samples, checksums and source/binary hashes are in `benchmarks.json`.
The only postmeasurement production-source change is a removed trailing blank
line; entire emitted C was compared byte for byte and is identical. Both source
hashes and the C hash are recorded. Other background jobs were running on this
machine; comparisons alternate order and use six samples with timing floors.
Do not treat these results as a controlled dedicated-machine guarantee.

Reproduction commands and public API: `docs/TREE_MAP.md`. The old recursive
proof closure applies only to `reference/legacy_balanced_search_tree.bend`.

The whole `PROOF.bend` gate was rerun and fails at the pre-existing obsolete
`DQ.DE{}` pattern (the current deque constructor has four fields). Exact
diagnostic: `full-proof.log`. This failure was not suppressed or reclassified.
