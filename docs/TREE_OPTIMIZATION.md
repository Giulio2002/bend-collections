# Red-black tree optimization, 22 September 2026

The implementation remains the same persistent red-black binary tree. Its
public API, comparator semantics, rotations, recolouring, error behavior, and
C reference are unchanged. No FFI or compiler/generated-C changes were used.

Previously `insert` searched the tree to decide whether to grow the cached
size, then traversed it again to insert. `remove` first searched for the old
value, then traversed again to delete. Both now return the old binding alongside
the update from one descent. Insertion still distinguishes replacement from a
new binding. Removal still returns the deleted value, or the exact unchanged
tree when the key is absent. The existing balancing routines are reused.

## Proofs

`proofs/balanced_search_tree/insert_fused.bend` proves that the fused descent
returns exactly `(old insertion, old lookup)` for arbitrary trees and comparator
decisions. `remove_fused.bend` proves the corresponding deletion equality and
that a missing key preserves the exact tree, including colours. Neither bridge
requires sortedness or a balancing premise.

The existing map operation and trace proofs now use these equivalences. The
complete `proofs/balanced_search_tree.bend` gate passes, with its existing order
and representation hypotheses and U32/String instances. This retains the
sorted-map specification, cached-size, red-black balancing, and trace laws;
it does not establish the unfinished whole-library proof gate or compiler
correctness. No axioms or unsafe declarations were added.

`tools/check_tree.py` runs 214 histories / 11,109 observations, combining an
independent Python dictionary oracle with runtime black-root, no-red-red,
black-height, sortedness, and cached-size checks. U32 and String keys are tested.
`tools/check_tree_fusion_mutations.py` checks that both fusion proofs reject
incorrect old-binding results in isolated copies.

## Measurements and remaining work

`tools/bench_tree_updates.py` compares an archived pre-change binary, the current
binary, and the unchanged optimized C reference. It uses the same pinned
workloads, six samples, alternating order, checksum equality, and the full
runner's >=50 ms Bend batch-difference threshold. Insert/remove benchmarks use
sizes 64, 4,096, and 131,072. Removal includes restoring insertion on both sides.

Insertion improves 2.07–2.33x and remove/reinsert improves 2.00–2.10x across those
sizes. The resulting 4.91–6.54x C ratios still fail the 2.5x target. The full
comparison, raw samples, and source hashes accompany the benchmark evidence.
Read-only operations are unchanged and remain slow, especially min/max.

Generated C shows reference-counted node consumption and generic payload work
in read paths. Accumulator traversal and broad template specialization were
tried in isolated experiments, but neither solved the read performance problem;
those experiments were not retained. The next task is reducing the cost of
reading nodes while preserving generic values and the existing laws. The
current results do not justify claiming that all tree operations are fast enough.

```sh
bend proofs/balanced_search_tree.bend
bend tests/balanced_search_tree/main.bend -o build/test-tree
python3 tools/check_tree.py
python3 tools/check_tree_fusion_mutations.py
python3 benchmarks/bench.py --build
python3 tools/bench_tree_updates.py --before /path/to/pre-change-binary
```
