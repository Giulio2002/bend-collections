# C DLL reference diagnostic, 2026-09-22

Bend still uses the ring deque. C now uses a reusable indexed DLL. These are
diagnostic timings, NOT same-algorithm acceptance of the DLL migration.

| Operation | Size class | Bend ns/op | C ns/op | Bend/C |
|---|---|---:|---:|---:|
| deque.push_front | small | 2.31 | 2.66 | 0.869 |
| deque.push_front | medium | 2.32 | 2.56 | 0.908 |
| deque.push_front | large | 3.04 | 3.57 | 0.851 |
| deque.push_back | small | 2.30 | 2.44 | 0.945 |
| deque.push_back | medium | 2.34 | 2.49 | 0.942 |
| deque.push_back | large | 3.03 | 3.50 | 0.865 |
| deque.peek_front | small | 1.00 | 1.01 | 0.992 |
| deque.peek_front | medium | 1.01 | 1.01 | 1.001 |
| deque.peek_front | large | 1.03 | 1.03 | 1.002 |
| deque.peek_back | small | 1.03 | 1.03 | 0.997 |
| deque.peek_back | medium | 1.01 | 1.01 | 0.999 |
| deque.peek_back | large | 1.01 | 1.01 | 1.001 |
| deque.length | small | 0.95 | 2.66 | 0.359 |
| deque.length | medium | 0.97 | 2.63 | 0.367 |
| deque.length | large | 0.97 | 2.62 | 0.372 |
| deque.to_list | small | 177.94 | 128.20 | 1.388 |
| deque.to_list | medium | 9166.67 | 3023.46 | 3.032 |
| deque.to_list | large | 464000.00 | 766296.00 | 0.606 |
| deque.pop_front | small | 2.00 | 6.28 | 0.319 |
| deque.pop_front | medium | 2.00 | 6.41 | 0.312 |
| deque.pop_front | large | 2.01 | 6.38 | 0.315 |
| deque.pop_back | small | 2.02 | 6.12 | 0.330 |
| deque.pop_back | medium | 2.01 | 6.13 | 0.328 |
| deque.pop_back | large | 2.02 | 6.21 | 0.326 |
| deque.new | small | 0.96 | 8.87 | 0.108 |
| deque.new | medium | 0.99 | 9.14 | 0.108 |
| deque.new | large | 1.00 | 9.04 | 0.110 |
| deque.new | edge-empty | 1.00 | 8.83 | 0.113 |
| deque.length | edge-empty | 1.01 | 2.73 | 0.369 |
| deque.push_front | edge-empty | 2.32 | 2.52 | 0.922 |
| deque.push_back | edge-empty | 2.32 | 2.51 | 0.926 |
| deque.pop_front | edge-empty | 0.99 | 3.19 | 0.310 |
| deque.pop_back | edge-empty | 0.99 | 3.29 | 0.300 |
| deque.peek_front | edge-empty | 1.00 | 1.00 | 0.991 |
| deque.peek_back | edge-empty | 0.99 | 1.00 | 0.983 |
| deque.to_list | edge-empty | 1.56 | 1.99 | 0.785 |
| queue.enqueue | small | 2.36 | 2.58 | 0.916 |
| queue.enqueue | medium | 2.32 | 2.53 | 0.917 |
| queue.enqueue | large | 3.07 | 3.64 | 0.842 |
| queue.peek | small | 1.01 | 1.01 | 1.001 |
| queue.peek | medium | 1.00 | 1.01 | 0.995 |
| queue.peek | large | 1.02 | 1.01 | 1.006 |
| queue.length | small | 1.00 | 2.70 | 0.371 |
| queue.length | medium | 1.00 | 2.69 | 0.372 |
| queue.length | large | 0.99 | 2.67 | 0.372 |
| queue.to_list | small | 177.94 | 129.34 | 1.376 |
| queue.to_list | medium | 9208.33 | 3001.46 | 3.068 |
| queue.to_list | large | 468000.00 | 760258.00 | 0.616 |
| queue.dequeue | small | 2.00 | 4.38 | 0.457 |
| queue.dequeue | medium | 1.99 | 4.62 | 0.432 |
| queue.dequeue | large | 2.01 | 4.43 | 0.453 |
| queue.new | small | 1.00 | 8.70 | 0.115 |
| queue.new | medium | 0.99 | 8.72 | 0.113 |
| queue.new | large | 1.00 | 8.68 | 0.116 |
| queue.new | edge-empty | 1.00 | 8.76 | 0.114 |
| queue.length | edge-empty | 1.00 | 2.75 | 0.364 |
| queue.enqueue | edge-empty | 2.34 | 2.48 | 0.946 |
| queue.dequeue | edge-empty | 1.00 | 3.24 | 0.309 |
| queue.peek | edge-empty | 1.00 | 1.02 | 0.981 |
| queue.to_list | edge-empty | 1.56 | 2.00 | 0.776 |

Original six-sample calibration, region ordering and checksum contract retained.
Failed measurements are not passes. Raw samples and source hashes accompany this table.
C correctness: ASan/UBSan, 200,000 model comparisons and 10 million constant-occupancy FIFO pairs passed.
Storage: 6,291,456-byte node capacity; optimized stress process peak RSS 4,587,520 bytes.
The operator snapshot still contains unfinished Bend DLL edits; no complete proof gate is claimed.
