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

## Whole-collection quick screen

This is provisional, not full-library acceptance. 119 operations, 31 above 2.5x, 4 unresolved; 40.575 seconds. One smallest nonempty workload per operation. Build time is separate. Up to three valid samples with alternating region order.

| Operation | Bend ns | C ns | Ratio | Samples | Status |
|---|---:|---:|---:|---:|---|
| dynamic_array.push | 12.297 | 3.357 | 3.663 | 2 | ESTIMATE |
| dynamic_array.get | 2.833 | 2.270 | 1.248 | 3 | ESTIMATE |
| dynamic_array.set | 2.222 | 2.157 | 1.030 | 3 | ESTIMATE |
| dynamic_array.length | 1.667 | 4.889 | 0.341 | 3 | ESTIMATE |
| dynamic_array.capacity | 1.500 | 3.861 | 0.388 | 3 | ESTIMATE |
| dynamic_array.reserve | 2.000 | 1.676 | 1.193 | 3 | ESTIMATE |
| dynamic_array.to_list | 250.000 | 104.100 | 2.402 | 3 | ESTIMATE |
| dynamic_array.clear | 65.104 | 8.558 | 7.608 | 3 | ESTIMATE |
| dynamic_array.pop | 5.917 | 3.800 | 1.557 | 2 | ESTIMATE |
| dynamic_array.new | 3.889 | 3.826 | 1.017 | 3 | ESTIMATE |
| deque.push_front | 21.701 | 15.191 | 1.429 | 3 | ESTIMATE |
| deque.push_back | 28.935 | 15.271 | 1.895 | 1 | ESTIMATE |
| deque.peek_front | 5.833 | 4.888 | 1.193 | 2 | ESTIMATE |
| deque.peek_back | 6.000 | 5.164 | 1.162 | 2 | ESTIMATE |
| deque.length | 1.500 | 3.489 | 0.430 | 3 | ESTIMATE |
| deque.to_list | 1050.000 | 971.850 | 1.080 | 3 | ESTIMATE |
| deque.pop_front | 7.333 | 15.456 | 0.474 | 1 | ESTIMATE |
| deque.pop_back | 8.333 | 14.648 | 0.569 | 3 | ESTIMATE |
| deque.new | 1.667 | 1.886 | 0.884 | 3 | ESTIMATE |
| queue.enqueue | 17.361 | 16.957 | 1.024 | 3 | ESTIMATE |
| queue.peek | 5.000 | 5.337 | 0.937 | 3 | ESTIMATE |
| queue.length | 1.389 | 4.397 | 0.316 | 3 | ESTIMATE |
| queue.to_list | 900.000 | 1031.750 | 0.872 | 3 | ESTIMATE |
| queue.dequeue | 20.000 | 13.603 | 1.470 | 3 | ESTIMATE |
| queue.new | 1.389 | 1.887 | 0.736 | 3 | ESTIMATE |
| stack.push | — | — | — | — | LOW_RESOLUTION |
| stack.peek | 2.167 | 1.499 | 1.446 | 1 | ESTIMATE |
| stack.length | 1.500 | 4.224 | 0.355 | 3 | ESTIMATE |
| stack.to_list | 650.000 | 32.500 | 20.000 | 3 | ESTIMATE |
| stack.pop | 3.333 | 17.756 | 0.188 | 3 | ESTIMATE |
| stack.new | 1.944 | 1.946 | 0.999 | 3 | ESTIMATE |
| doubly_linked_list.push_front | 13.021 | 7.303 | 1.783 | 1 | ESTIMATE |
| doubly_linked_list.push_back | 26.042 | 6.589 | 3.953 | 3 | ESTIMATE |
| doubly_linked_list.insert_before | 17.361 | 6.194 | 2.803 | 3 | ESTIMATE |
| doubly_linked_list.insert_after | 21.701 | 5.916 | 3.668 | 3 | ESTIMATE |
| doubly_linked_list.get | 3.000 | 2.262 | 1.326 | 3 | ESTIMATE |
| doubly_linked_list.set | 2.500 | 1.981 | 1.262 | 3 | ESTIMATE |
| doubly_linked_list.next | 2.778 | 2.645 | 1.050 | 3 | ESTIMATE |
| doubly_linked_list.prev | 3.889 | 2.591 | 1.501 | 3 | ESTIMATE |
| doubly_linked_list.length | 1.389 | 4.019 | 0.346 | 3 | ESTIMATE |
| doubly_linked_list.to_list | 266.667 | 156.933 | 1.699 | 3 | ESTIMATE |
| doubly_linked_list.remove | 12.297 | 9.890 | 1.243 | 2 | ESTIMATE |
| doubly_linked_list.new | 16.667 | 4.262 | 3.911 | 3 | ESTIMATE |
| binary_heap.push | 21.701 | 13.980 | 1.552 | 3 | ESTIMATE |
| binary_heap.peek | 1.667 | 1.546 | 1.078 | 3 | ESTIMATE |
| binary_heap.length | 1.944 | 4.457 | 0.436 | 3 | ESTIMATE |
| binary_heap.from_list | 160.000 | 88.680 | 1.804 | 3 | ESTIMATE |
| binary_heap.to_sorted_list | 1166.667 | 809.333 | 1.442 | 3 | ESTIMATE |
| binary_heap.pop | 50.000 | 27.900 | 1.792 | 3 | ESTIMATE |
| binary_heap.new | 5.000 | 4.164 | 1.201 | 2 | ESTIMATE |
| balanced_search_tree.insert | 694.444 | 70.573 | 9.840 | 3 | ESTIMATE |
| balanced_search_tree.remove | 1190.000 | 95.080 | 12.516 | 1 | ESTIMATE |
| balanced_search_tree.lookup | 200.000 | 28.760 | 6.954 | 3 | ESTIMATE |
| balanced_search_tree.contains | 210.000 | 33.430 | 6.282 | 3 | ESTIMATE |
| balanced_search_tree.min | 70.000 | 2.350 | 29.787 | 3 | ESTIMATE |
| balanced_search_tree.max | 90.000 | 2.620 | 34.351 | 3 | ESTIMATE |
| balanced_search_tree.lower_bound | 190.000 | 29.910 | 6.352 | 3 | ESTIMATE |
| balanced_search_tree.range | 325.000 | 51.092 | 6.361 | 3 | ESTIMATE |
| balanced_search_tree.to_list | 916.667 | 73.667 | 12.443 | 3 | ESTIMATE |
| balanced_search_tree.length | 1.389 | 4.166 | 0.333 | 3 | ESTIMATE |
| balanced_search_tree.new | 1.389 | 3.508 | 0.396 | 3 | ESTIMATE |
| bitset.set | 2.222 | 1.974 | 1.125 | 3 | ESTIMATE |
| bitset.clear | 2.194 | 2.045 | 1.073 | 1 | ESTIMATE |
| bitset.get | 2.500 | 2.077 | 1.204 | 3 | ESTIMATE |
| bitset.count | 20.000 | 6.660 | 3.003 | 3 | ESTIMATE |
| bitset.length | 1.500 | 5.013 | 0.299 | 3 | ESTIMATE |
| bitset.to_list | 200.000 | 110.500 | 1.810 | 3 | ESTIMATE |
| bitset.union | 3.333 | 1.928 | 1.729 | 3 | ESTIMATE |
| bitset.intersection | 2.333 | 1.787 | 1.305 | 3 | ESTIMATE |
| bitset.difference | 2.333 | 1.811 | 1.289 | 3 | ESTIMATE |
| bitset.xor | 2.000 | 1.757 | 1.139 | 3 | ESTIMATE |
| bitset.new | 4.167 | 17.250 | 0.242 | 1 | ESTIMATE |
| lru.add | 220.000 | 15.300 | 14.379 | 3 | ESTIMATE |
| lru.get | 180.000 | 17.980 | 10.011 | 3 | ESTIMATE |
| lru.peek | 170.000 | 16.770 | 10.137 | 3 | ESTIMATE |
| lru.contains | 170.000 | 2.460 | 69.106 | 3 | ESTIMATE |
| lru.remove | 740.000 | 19.540 | 37.871 | 3 | ESTIMATE |
| lru.purge | 20833.333 | 598.958 | 34.783 | 3 | ESTIMATE |
| lru.resize | 12152.778 | 350.694 | 34.653 | 3 | ESTIMATE |
| lru.keys | 850.000 | 132.000 | 6.439 | 3 | ESTIMATE |
| lru.len | 1.667 | 4.388 | 0.380 | 3 | ESTIMATE |
| lru.new | 50.000 | 12.770 | 3.915 | 3 | ESTIMATE |
| lru.capacity | 1.667 | 4.395 | 0.379 | 3 | ESTIMATE |
| lru.set_lifetime | 2530.000 | 9.110 | 277.717 | 1 | ESTIMATE |
| lru.metrics | — | — | — | — | TIMEOUT |
| lru.expiry | 18229.167 | 78.125 | 233.333 | 2 | ESTIMATE |
| lru.remove_seq | — | — | — | — | TIMEOUT |
| lru.purge_isolated | 1041.667 | 114.062 | 9.132 | 1 | ESTIMATE |
| lru.resize_isolated | — | — | — | — | TIMEOUT |
| lifo_queue.put | 13.021 | 21.910 | 0.594 | 3 | ESTIMATE |
| lifo_queue.peek | 2.333 | 1.558 | 1.498 | 3 | ESTIMATE |
| lifo_queue.qsize | 1.167 | 3.755 | 0.311 | 3 | ESTIMATE |
| lifo_queue.to_list | 500.000 | 29.700 | 16.835 | 3 | ESTIMATE |
| lifo_queue.get | 3.417 | 16.075 | 0.213 | 2 | ESTIMATE |
| lifo_queue.new | 1.833 | 1.654 | 1.109 | 3 | ESTIMATE |
| simple_queue.put | 21.701 | 21.602 | 1.005 | 3 | ESTIMATE |
| simple_queue.peek | 5.167 | 5.323 | 0.971 | 3 | ESTIMATE |
| simple_queue.qsize | 1.333 | 3.578 | 0.373 | 3 | ESTIMATE |
| simple_queue.to_list | 850.000 | 957.750 | 0.887 | 3 | ESTIMATE |
| simple_queue.get | 30.000 | 11.515 | 2.605 | 2 | ESTIMATE |
| simple_queue.new | 1.167 | 1.610 | 0.725 | 3 | ESTIMATE |
| priority_queue.put | 21.701 | 14.783 | 1.468 | 3 | ESTIMATE |
| priority_queue.peek | 1.500 | 1.526 | 0.983 | 3 | ESTIMATE |
| priority_queue.qsize | 1.500 | 3.910 | 0.384 | 3 | ESTIMATE |
| priority_queue.from_list | 120.000 | 69.020 | 1.739 | 3 | ESTIMATE |
| priority_queue.to_sorted_list | 1500.000 | 631.000 | 2.377 | 1 | ESTIMATE |
| priority_queue.get | 40.000 | 16.670 | 2.400 | 3 | ESTIMATE |
| priority_queue.new | 2.778 | 3.303 | 0.841 | 3 | ESTIMATE |
| dlist_iterator.iter_first | 6.667 | 4.870 | 1.369 | 3 | ESTIMATE |
| dlist_iterator.iter_last | 6.667 | 5.271 | 1.265 | 3 | ESTIMATE |
| dlist_iterator.next | 2.667 | 2.750 | 0.970 | 3 | ESTIMATE |
| dlist_iterator.previous | 2.667 | 3.121 | 0.854 | 3 | ESTIMATE |
| dlist_iterator.set | 1.667 | 1.703 | 0.979 | 3 | ESTIMATE |
| dlist_iterator.add | 13.000 | 9.313 | 1.396 | 3 | ESTIMATE |
| dlist_iterator.remove | 11.667 | 8.918 | 1.308 | 3 | ESTIMATE |
| dlist_iterator.has_next | 1.333 | 1.537 | 0.867 | 3 | ESTIMATE |
| dlist_iterator.has_previous | 1.667 | 1.400 | 1.190 | 3 | ESTIMATE |
| dlist_iterator.position | 1.000 | 1.397 | 0.716 | 3 | ESTIMATE |
| dlist_iterator.finish | 6.667 | 4.488 | 1.486 | 3 | ESTIMATE |
