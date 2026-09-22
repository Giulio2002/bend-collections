# Bend versus optimized C benchmarks

## DLL iterators: calibrated acceptance passed

All **33/33** rows pass the **2.5x** target (11 operations, three sizes). Six samples per row, alternating A/B/C order; every Bend A−B difference is at least 50 ms. All checksums match. Worst ratio of medians: **1.575x**. Worst individual sample ratio: **1.848x**.

| Operation | n=64 | n=4,096 | n=65,536 |
|---|---:|---:|---:|
| dlist_iterator.iter_first | 1.388x | 1.409x | 1.376x |
| dlist_iterator.iter_last | 1.246x | 1.274x | 1.291x |
| dlist_iterator.next | 0.989x | 0.865x | 0.556x |
| dlist_iterator.previous | 0.558x | 0.539x | 0.507x |
| dlist_iterator.set | 1.051x | 1.067x | 1.004x |
| dlist_iterator.add | 1.315x | 1.236x | 1.373x |
| dlist_iterator.remove | 1.334x | 1.319x | 1.313x |
| dlist_iterator.has_next | 0.905x | 1.017x | 0.998x |
| dlist_iterator.has_previous | 1.067x | 0.938x | 1.037x |
| dlist_iterator.position | 0.901x | 0.930x | 0.959x |
| dlist_iterator.finish | 1.456x | 1.454x | 1.575x |

Ratios are Bend/C. Add/remove rows measure **add + previous + remove**, not an isolated call. First/last/finish include finish/recreate. [API and methodology](docs/DLIST_ITERATOR.md). [Complete sample evidence](benchmarks/evidence/iterator-20260922/calibrated.json), [raw timings](benchmarks/evidence/iterator-20260922/samples.log). C sources are unchanged from the pre-optimization iterator baseline. Stock Bend 2.0.16, no FFI or generated-C edits.

## Red-black tree updates

One-descent insertion and deletion preserve the existing API and tree representation. The complete tree proof module, 11,109 differential/structural observations, and proof mutation checks pass. The full-library proof gate remains incomplete. C is unchanged.

| Operation | Size | Before ns | After ns | C ns | Speedup | Bend/C |
|---|---:|---:|---:|---:|---:|---:|
| balanced_search_tree.insert | 64 | 515.83 | 221.67 | 33.90 | 2.327x | 6.539x |
| balanced_search_tree.insert | 4096 | 1240.00 | 535.00 | 85.72 | 2.318x | 6.241x |
| balanced_search_tree.insert | 131072 | 2140.05 | 1033.78 | 197.69 | 2.070x | 5.229x |
| balanced_search_tree.remove | 64 | 975.00 | 463.33 | 76.53 | 2.104x | 6.055x |
| balanced_search_tree.remove | 4096 | 1950.00 | 955.00 | 157.95 | 2.042x | 6.046x |
| balanced_search_tree.remove | 131072 | 2793.75 | 1400.00 | 284.89 | 1.996x | 4.914x |

Six samples per row, calibrated batch differences. Remove includes restoring insertion. **All six update rows remain above the 2.5x target.** Read paths are unchanged. [Methodology and proofs](docs/TREE_OPTIMIZATION.md); [raw samples and hashes](benchmarks/evidence/tree-updates-20260922/calibrated.json).

## Whole-collection quick screen

Provisional, not full-library acceptance: **84 within target, 28 too slow, 7 unresolved** out of 119 operations; 39.931 seconds excluding build. Smallest nonempty workload, short noisy measurements. Changes in classification alone do not establish speedups.

| Operation | Bend ns | C ns | Ratio | Samples | Status |
|---|---:|---:|---:|---:|---|
| dynamic_array.push | 5.787 | 3.141 | 1.842 | 3 | ESTIMATE |
| dynamic_array.get | 2.333 | 1.698 | 1.374 | 3 | ESTIMATE |
| dynamic_array.set | 1.667 | 1.642 | 1.015 | 3 | ESTIMATE |
| dynamic_array.length | 1.667 | 3.604 | 0.462 | 2 | ESTIMATE |
| dynamic_array.capacity | 1.167 | 2.890 | 0.404 | 3 | ESTIMATE |
| dynamic_array.reserve | 1.389 | 1.269 | 1.095 | 3 | ESTIMATE |
| dynamic_array.to_list | 200.000 | 85.950 | 2.327 | 3 | ESTIMATE |
| dynamic_array.clear | 60.764 | 6.962 | 8.728 | 3 | ESTIMATE |
| dynamic_array.pop | 4.917 | 3.548 | 1.386 | 2 | ESTIMATE |
| dynamic_array.new | 2.250 | 3.735 | 0.602 | 2 | ESTIMATE |
| deque.push_front | 18.808 | 14.899 | 1.262 | 1 | ESTIMATE |
| deque.push_back | 21.701 | 12.457 | 1.742 | 1 | ESTIMATE |
| deque.peek_front | 5.000 | 4.494 | 1.113 | 2 | ESTIMATE |
| deque.peek_back | 5.000 | 4.542 | 1.101 | 3 | ESTIMATE |
| deque.length | 1.333 | 3.296 | 0.405 | 3 | ESTIMATE |
| deque.to_list | 900.000 | 839.450 | 1.072 | 3 | ESTIMATE |
| deque.pop_front | 6.833 | 4.656 | 1.468 | 1 | ESTIMATE |
| deque.pop_back | 8.333 | 13.650 | 0.611 | 3 | ESTIMATE |
| deque.new | 1.389 | 2.093 | 0.664 | 3 | ESTIMATE |
| queue.enqueue | 21.701 | 18.294 | 1.186 | 3 | ESTIMATE |
| queue.peek | 5.000 | 5.657 | 0.884 | 2 | ESTIMATE |
| queue.length | 1.667 | 4.252 | 0.392 | 3 | ESTIMATE |
| queue.to_list | 800.000 | 828.450 | 0.966 | 3 | ESTIMATE |
| queue.dequeue | 20.000 | 12.787 | 1.564 | 3 | ESTIMATE |
| queue.new | 1.333 | 1.726 | 0.773 | 3 | ESTIMATE |
| stack.push | 13.021 | 15.200 | 0.857 | 3 | ESTIMATE |
| stack.peek | 2.167 | 1.315 | 1.648 | 3 | ESTIMATE |
| stack.length | 1.333 | 3.489 | 0.382 | 3 | ESTIMATE |
| stack.to_list | 500.000 | 27.350 | 18.282 | 3 | ESTIMATE |
| stack.pop | 2.778 | 14.603 | 0.190 | 2 | ESTIMATE |
| stack.new | 1.333 | 1.335 | 0.999 | 3 | ESTIMATE |
| doubly_linked_list.push_front | 17.361 | 5.603 | 3.098 | 3 | ESTIMATE |
| doubly_linked_list.push_back | — | — | — | — | LOW_RESOLUTION |
| doubly_linked_list.insert_before | 17.361 | 5.174 | 3.356 | 3 | ESTIMATE |
| doubly_linked_list.insert_after | 15.191 | 4.323 | 3.514 | 2 | ESTIMATE |
| doubly_linked_list.get | 2.250 | 1.699 | 1.325 | 1 | ESTIMATE |
| doubly_linked_list.set | 2.333 | 1.659 | 1.407 | 3 | ESTIMATE |
| doubly_linked_list.next | 2.778 | 2.217 | 1.253 | 3 | ESTIMATE |
| doubly_linked_list.prev | 2.833 | 2.209 | 1.282 | 3 | ESTIMATE |
| doubly_linked_list.length | 1.667 | 3.722 | 0.448 | 3 | ESTIMATE |
| doubly_linked_list.to_list | 266.667 | 150.200 | 1.775 | 3 | ESTIMATE |
| doubly_linked_list.remove | 10.127 | 8.424 | 1.202 | 3 | ESTIMATE |
| doubly_linked_list.new | 13.333 | 3.373 | 3.953 | 3 | ESTIMATE |
| binary_heap.push | 21.701 | 12.797 | 1.696 | 1 | ESTIMATE |
| binary_heap.peek | 1.389 | 1.501 | 0.925 | 3 | ESTIMATE |
| binary_heap.length | 1.389 | 4.542 | 0.306 | 3 | ESTIMATE |
| binary_heap.from_list | 120.000 | 66.980 | 1.792 | 3 | ESTIMATE |
| binary_heap.to_sorted_list | 1083.333 | 666.750 | 1.625 | 3 | ESTIMATE |
| binary_heap.pop | 70.000 | 36.710 | 1.907 | 3 | ESTIMATE |
| binary_heap.new | 6.333 | 4.795 | 1.321 | 2 | ESTIMATE |
| balanced_search_tree.insert | 347.222 | 67.882 | 5.115 | 3 | ESTIMATE |
| balanced_search_tree.remove | 615.000 | 132.285 | 4.649 | 2 | ESTIMATE |
| balanced_search_tree.lookup | 210.000 | 33.980 | 6.180 | 3 | ESTIMATE |
| balanced_search_tree.contains | 250.000 | 33.490 | 7.465 | 3 | ESTIMATE |
| balanced_search_tree.min | 80.000 | 1.930 | 41.451 | 3 | ESTIMATE |
| balanced_search_tree.max | 80.000 | 2.650 | 30.189 | 3 | ESTIMATE |
| balanced_search_tree.lower_bound | 180.000 | 28.090 | 6.408 | 3 | ESTIMATE |
| balanced_search_tree.range | 291.667 | 42.667 | 6.836 | 3 | ESTIMATE |
| balanced_search_tree.to_list | 1500.000 | 70.500 | 21.277 | 1 | ESTIMATE |
| balanced_search_tree.length | 1.333 | 3.725 | 0.358 | 3 | ESTIMATE |
| balanced_search_tree.new | 1.333 | 3.044 | 0.438 | 3 | ESTIMATE |
| bitset.set | 1.667 | 1.563 | 1.066 | 3 | ESTIMATE |
| bitset.clear | 1.389 | 1.546 | 0.898 | 3 | ESTIMATE |
| bitset.get | 1.972 | 1.605 | 1.229 | 1 | ESTIMATE |
| bitset.count | 13.333 | 4.747 | 2.809 | 3 | ESTIMATE |
| bitset.length | 1.167 | 3.309 | 0.353 | 3 | ESTIMATE |
| bitset.to_list | 150.000 | 76.200 | 1.969 | 3 | ESTIMATE |
| bitset.union | 1.667 | 1.208 | 1.379 | 3 | ESTIMATE |
| bitset.intersection | 3.333 | 1.463 | 2.279 | 3 | ESTIMATE |
| bitset.difference | 1.667 | 1.349 | 1.235 | 3 | ESTIMATE |
| bitset.xor | 2.667 | 1.350 | 1.975 | 3 | ESTIMATE |
| bitset.new | 3.250 | 12.017 | 0.270 | 2 | ESTIMATE |
| lru.add | 170.000 | 12.470 | 13.633 | 3 | ESTIMATE |
| lru.get | 160.000 | 13.990 | 11.437 | 3 | ESTIMATE |
| lru.peek | 140.000 | 13.870 | 10.094 | 3 | ESTIMATE |
| lru.contains | 140.000 | 2.010 | 69.652 | 3 | ESTIMATE |
| lru.remove | 720.000 | 19.670 | 36.604 | 3 | ESTIMATE |
| lru.purge | 20833.333 | 531.250 | 39.216 | 3 | ESTIMATE |
| lru.resize | 15625.000 | 296.875 | 52.632 | 3 | ESTIMATE |
| lru.keys | 700.000 | 119.150 | 5.875 | 3 | ESTIMATE |
| lru.len | 1.500 | 3.813 | 0.393 | 3 | ESTIMATE |
| lru.new | 23.333 | 11.067 | 2.108 | 3 | ESTIMATE |
| lru.capacity | 1.278 | 3.536 | 0.361 | 1 | ESTIMATE |
| lru.set_lifetime | 2010.000 | 8.530 | 235.639 | 1 | ESTIMATE |
| lru.metrics | — | — | — | — | TIMEOUT |
| lru.expiry | 10416.667 | 32.552 | 320.000 | 2 | ESTIMATE |
| lru.remove_seq | — | — | — | — | TIMEOUT |
| lru.purge_isolated | — | — | — | — | TIMEOUT |
| lru.resize_isolated | — | — | — | — | TIMEOUT |
| lifo_queue.put | — | — | — | — | LOW_RESOLUTION |
| lifo_queue.peek | 2.389 | 1.576 | 1.516 | 2 | ESTIMATE |
| lifo_queue.qsize | 1.500 | 4.662 | 0.322 | 3 | ESTIMATE |
| lifo_queue.to_list | 650.000 | 29.850 | 21.776 | 3 | ESTIMATE |
| lifo_queue.get | 2.778 | 15.202 | 0.183 | 3 | ESTIMATE |
| lifo_queue.new | 1.500 | 1.408 | 1.065 | 3 | ESTIMATE |
| simple_queue.put | 13.021 | 11.610 | 1.121 | 3 | ESTIMATE |
| simple_queue.peek | 4.444 | 4.557 | 0.975 | 3 | ESTIMATE |
| simple_queue.qsize | 1.222 | 3.689 | 0.331 | 2 | ESTIMATE |
| simple_queue.to_list | 800.000 | 845.550 | 0.946 | 3 | ESTIMATE |
| simple_queue.get | 16.667 | 12.195 | 1.367 | 3 | ESTIMATE |
| simple_queue.new | 1.333 | 1.598 | 0.834 | 3 | ESTIMATE |
| priority_queue.put | — | — | — | — | LOW_RESOLUTION |
| priority_queue.peek | 1.167 | 1.301 | 0.897 | 3 | ESTIMATE |
| priority_queue.qsize | 1.333 | 3.868 | 0.345 | 3 | ESTIMATE |
| priority_queue.from_list | 120.000 | 69.740 | 1.721 | 3 | ESTIMATE |
| priority_queue.to_sorted_list | 1083.333 | 694.167 | 1.561 | 3 | ESTIMATE |
| priority_queue.get | 50.000 | 19.950 | 2.506 | 3 | ESTIMATE |
| priority_queue.new | 3.167 | 3.482 | 0.909 | 3 | ESTIMATE |
| dlist_iterator.iter_first | 5.556 | 4.203 | 1.322 | 3 | ESTIMATE |
| dlist_iterator.iter_last | 6.000 | 4.830 | 1.242 | 3 | ESTIMATE |
| dlist_iterator.next | 2.556 | 2.369 | 1.079 | 3 | ESTIMATE |
| dlist_iterator.previous | 2.333 | 2.710 | 0.861 | 3 | ESTIMATE |
| dlist_iterator.set | 1.333 | 1.293 | 1.031 | 3 | ESTIMATE |
| dlist_iterator.add | 10.000 | 7.737 | 1.293 | 3 | ESTIMATE |
| dlist_iterator.remove | 10.000 | 8.283 | 1.207 | 2 | ESTIMATE |
| dlist_iterator.has_next | 1.296 | 1.326 | 0.977 | 3 | ESTIMATE |
| dlist_iterator.has_previous | 1.667 | 1.296 | 1.286 | 3 | ESTIMATE |
| dlist_iterator.position | 1.667 | 1.315 | 1.267 | 1 | ESTIMATE |
| dlist_iterator.finish | 6.667 | 4.191 | 1.591 | 3 | ESTIMATE |
