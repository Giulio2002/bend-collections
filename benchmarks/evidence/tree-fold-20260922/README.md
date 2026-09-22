# Public TreeMap bulk folds

Stock Bend 2.0.16; unchanged optimized C reference. Before is commit `8274d4f` and uses editable iterators to perform the fold. After uses the new public `fold`/`view_fold` with a Data accumulator and static visitor. Both compute identical ordered folds over identical inputs, without output lists. This is a new bulk API optimization, not a claim about the per-item editable-iterator API.

Map headers stay outside the loop. Each visited entry feeds the visitor directly, without reconstructing an editable cursor or optional entry. The terminal node is resolved once; initial membership validation handles empty/equal-exclusive ranges before traversal. Storage and parent-link successor algorithm remain unchanged. No FFI or custom compiler/generated-C patches.

Six alternating before/after/C samples. Batches use three times the previous calibrated traversal counts, and every sample must meet the existing Bend/C delta floors. Checksums agree. Other jobs were running: compare paired results in this run, not absolute timings across historical runs. A preliminary run with noisy adaptive calibration was abandoned before completion, not counted as evidence here.

| Operation | Size | Before µs | Fold µs | C µs | Speedup | Fold / C |
|---|---:|---:|---:|---:|---:|---:|
| tree_map.range | 64 | 0.277 | 0.204 | 0.054 | 1.36× | 3.75× |
| tree_map.range | 4096 | 15.572 | 10.392 | 1.369 | 1.50× | 7.59× |
| tree_map.range | 131072 | 92.949 | 61.218 | 8.199 | 1.52× | 7.47× |
| tree_map.iterate | 64 | 0.806 | 0.436 | 0.051 | 1.85× | 8.49× |
| tree_map.iterate | 4096 | 70.098 | 42.451 | 3.490 | 1.65× | 12.16× |
| tree_map.iterate | 131072 | 3115.152 | 2354.545 | 315.142 | 1.32× | 7.47× |

All six rows remain above 2.5× C. This is partial performance progress. Other operations were not rebenchmarked. A typed-bound branch was separately screened, regressed the small range case, and was reverted; its screen is retained as rejected-experiment evidence.

Validation: the fold-backed driver passes 300 histories / 92,544 operations using the existing independent dictionary/structural oracle. Additional exact-output tests cover 7,680 bounded traversals (all inclusive/exclusive combinations, equal bounds, ascending/descending, ordinary/reverse/equivalence-class comparators) and check the whole arena is unchanged after every fold.

`TREE_FOLD_PROOF.bend` adds six public component laws for empty and singleton maps, two-entry ordering in both directions, equal-exclusive emptiness, and exclusive upper bounds. A semantic mutation that includes the exclusive endpoint is rejected by the latter law. Existing component and traversal laws still pass. These laws **do not establish universal arbitrary-tree fold refinement**, and the indexed TreeMap still lacks its full invariant/refinement proofs. No performance or proof acceptance claim is made.

Reproduce from the repository root:

```
mkdir -p build/tree-fold
bend benchmarks/bend/balanced_search_tree.bend -o build/tree-fold/after
# Build the same driver at 8274d4f into build/tree-fold/before.
# Build the existing unchanged C reference with the repository benchmark harness.
python3 tools/bench_tree_folds.py
bend tests/tree_map/fold.bend -o build/tree-fold/test
python3 tools/check_tree_map.py --binary build/tree-fold/test --report build/tree-fold/tests.json
python3 tools/check_tree_folds.py
bend TREE_FOLD_PROOF.bend
bend TREE_RANGE_PROOF.bend
```
