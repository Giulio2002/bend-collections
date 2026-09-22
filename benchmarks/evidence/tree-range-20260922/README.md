# TreeMap range/iteration overhead reduction

Stock Bend 2.0.16, unchanged optimized C reference and workloads. No FFI or hand-edited generated C. Baseline is private repository commit `958a0a3`; both binaries were measured in alternating order alongside C, with six samples, calibration floors and matching checksums. Raw samples, environment and hashes are in `benchmarks.json`.

The successor walk now passes only its node buffer through parent/child loops and reconstructs the map header once on return. A direct branch replaces the polymorphic `pick(Ascend, ...)`, avoiding boxed traversal-state construction. Bounds, fuel limits, missing-slot behavior and owning cursor API remain unchanged. An earlier attempt to fuse the current-node read did not improve performance and was discarded.

| Operation | Size | Before µs | After µs | C µs | Speedup | After / C |
|---|---:|---:|---:|---:|---:|---:|
| tree_map.range | 64 | 0.208 | 0.145 | 0.031 | 1.43× | 4.71× |
| tree_map.range | 4096 | 12.990 | 7.843 | 0.809 | 1.66× | 9.69× |
| tree_map.range | 131072 | 117.548 | 81.010 | 8.028 | 1.45× | 10.09× |
| tree_map.iterate | 64 | 1.022 | 0.676 | 0.046 | 1.51× | 14.59× |
| tree_map.iterate | 4096 | 83.676 | 53.824 | 3.180 | 1.55× | 16.93× |
| tree_map.iterate | 131072 | 2854.545 | 2218.182 | 214.027 | 1.29× | 10.36× |

All six rows still miss the 2.5× target. Other operations were not rebenchmarked: the previous full sweep is historical evidence, not a fresh full-library acceptance run. Time per range/iteration is per complete traversal workload, not per entry.

Validation: 300 independent histories / 92,544 operations passed, checking contents, ordering, red-black invariants, parent links and storage reuse after every operation. The existing 16 component laws pass. `TREE_RANGE_PROOF.bend` adds three universally quantified local laws: the new branch equals the original choice, slot-result handling preserves the buffer, and an ascent step preserves the buffer. These do **not** prove complete old/new traversal equivalence or indexed TreeMap refinement. Full indexed TreeMap proofs remain open; the root proof gate also retains its previously reported unrelated deque incompatibility.

Reproduce: build the baseline revision's `benchmarks/bend/balanced_search_tree.bend` into `build/tree-range/before`, build the current driver into `build/tree-range/narrow`, build the existing C reference, then run `python3 tools/bench_tree_ranges.py`. Run `bend TREE_MAP_COMPONENT_PROOF.bend`, `bend TREE_RANGE_PROOF.bend`, compile `tests/tree_map/main.bend` to `build/tree-map/test`, and run `python3 tools/check_tree_map.py`.
