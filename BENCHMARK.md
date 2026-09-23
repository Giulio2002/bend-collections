# Benchmarks

Every row runs the same algorithm in Bend (native C backend, one thread) and in C
(`-O3 -march=native`), with identical inputs, and the two results must agree
(a checksum of every result, or the full digests). **Ratio = Bend time / C time**:
below 1 Bend is faster. The target is 3x (`benchmarks/contract.json`).

Machine: arm64, macOS-15.6-arm64-arm-64bit-Mach-O. Measured while other work was running on the machine, so
absolute times are noisy; each sample alternates Bend and C under the same load,
so the ratios are the meaningful column.

Reproduce:

```sh
python3 benchmarks/full_sweep.py --report build/bench/full.json   # containers
python3 benchmarks/crypto.py --report build/bench/crypto.json      # hashes
python3 benchmarks/render.py                                        # this file
```

## Hashes

Median of five alternating samples per size, after a warm-up; inputs prepared
before the timed region. Microseconds per hash.

### SHA-256

C reference: portable FIPS 180-4 C (`benchmarks/native/sha256.c`). Worst ratio 2.06.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 64 B | 0.90 | 0.70 | 1.29 |
| 1 KiB | 8.79 | 4.26 | 2.06 |
| 16 KiB | 125 | 65.1 | 1.92 |
| 64 KiB | 516 | 359 | 1.44 |
| 1 MiB | 9750 | 5346 | 1.82 |

### Keccak-256

C reference: XKCP `plain-64bits` fully unrolled (`benchmarks/native/xkcp/`). Worst ratio 4.06.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.88 | 0.24 | 3.63 |
| 64 B | 0.89 | 0.24 | 3.64 |
| 1 KiB | 7.26 | 1.85 | 3.93 |
| 16 KiB | 105 | 27.5 | 3.83 |
| 64 KiB | 453 | 112 | 4.06 |
| 1 MiB | 6438 | 2048 | 3.14 |

### BLAKE2s

C reference: official BLAKE2 reference `blake2s-ref.c`. Worst ratio 1.15.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.14 | 0.14 | 1.07 |
| 64 B | 0.13 | 0.12 | 1.11 |
| 1 KiB | 2.20 | 1.91 | 1.15 |
| 16 KiB | 28.3 | 27.6 | 1.03 |
| 64 KiB | 141 | 144 | 0.98 |
| 1 MiB | 1875 | 2048 | 0.92 |

### BLAKE2b

C reference: official BLAKE2 reference `blake2b-ref.c`. Worst ratio 2.95.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.43 | 0.14 | 2.95 |
| 64 B | 0.42 | 0.17 | 2.54 |
| 1 KiB | 2.81 | 1.06 | 2.65 |
| 16 KiB | 44.9 | 17.1 | 2.63 |
| 64 KiB | 195 | 76.2 | 2.56 |
| 1 MiB | 2688 | 1072 | 2.51 |

### BLAKE3

C reference: official BLAKE3 C, portable only (no SIMD). Worst ratio 1.59.

| Message | Bend (us) | C (us) | Ratio |
|---:|---:|---:|---:|
| 0 B | 0.17 | 0.11 | 1.59 |
| 64 B | 0.13 | 0.11 | 1.21 |
| 1 KiB | 1.65 | 1.48 | 1.11 |
| 16 KiB | 24.4 | 20.4 | 1.20 |
| 64 KiB | 89.8 | 91.6 | 0.98 |
| 1 MiB | 1438 | 1330 | 1.08 |

## Containers

**327 of 378 container rows are still being measured; they show as pending.**

Each row measures one public operation at three structure sizes. The time of
an operation is the difference between two regions that run 2k and k of them
(build, settle and teardown cancel); removals are measured in a restoring pair
with the insertion that puts the element back. Nanoseconds per operation,
median of six samples. See `benchmarks/run.py` for the method.

### Dynamic array

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 25.9 | 10.7 | 2.42 |
| push | medium | 25.0 | 10.1 | 2.48 |
| push | large | 46.8 | 22.3 | 2.09 |
| get | small | 22.8 | 3.63 | 6.27 (over 3x) |
| get | medium | 22.0 | 3.27 | 6.72 (over 3x) |
| get | large | | | not timeable |
| set | small | 5.90 | 3.44 | 1.72 |
| set | medium | | | not timeable |
| set | large | | | not timeable |
| length | small | 1.62 | 4.75 | 0.34 |
| length | medium | 1.65 | 5.37 | 0.31 |
| length | large | 1.63 | 4.89 | 0.33 |
| capacity | small | 1.54 | 4.02 | 0.38 |
| capacity | medium | 1.53 | 5.32 | 0.29 |
| capacity | large | 1.42 | 4.33 | 0.33 |
| reserve | small | | | not timeable |
| reserve | medium | | | not timeable |
| reserve | large | 2.54 | 2.99 | 0.85 |
| to_list | small | 329 | 152 | 2.17 |
| to_list | medium | 20429 | 10592 | 1.93 |
| to_list | large | 933333 | 650377 | 1.44 |
| clear | small | 342 | 13.3 | 25.74 (over 3x) |
| clear | medium | | | not timeable |
| clear | large | 1354000 | 17795 | 76.09 (over 3x) |
| pop | small | 12.4 | 6.49 | 1.91 |
| pop | medium | 8.63 | 6.52 | 1.32 |
| pop | large | 8.36 | 6.73 | 1.24 |
| new | small | 12.7 | 3.79 | 3.35 (over 3x) |
| new | medium | 10.0 | 3.60 | 2.79 |
| new | large | 18.5 | 4.00 | 4.63 (over 3x) |

### Deque

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | 35.6 | 33.7 | 1.06 |
| push_front | medium | 26.9 | 29.4 | 0.91 |
| push_front | large | 20.1 | 35.3 | 0.57 |
| push_back | small | 28.6 | 22.7 | 1.26 |
| push_back | medium | 26.7 | 30.8 | 0.87 |
| push_back | large | | | not timeable |
| peek_front | small | | | not timeable |
| peek_front | medium | 6.37 | 5.07 | 1.26 |
| peek_front | large | 6.05 | 4.72 | 1.28 |
| peek_back | small | 6.64 | 4.75 | 1.40 |
| peek_back | medium | 5.64 | 4.47 | 1.26 |
| peek_back | large | 5.74 | 4.43 | 1.30 |
| length | small | 1.45 | 3.54 | 0.41 |
| length | medium | 1.39 | 3.54 | 0.39 |
| length | large | 1.40 | 3.88 | 0.36 |
| to_list | small | 1003 | 1080 | 0.93 |
| to_list | medium | 80500 | 68602 | 1.17 |
| to_list | large | 4910000 | 5167120 | 0.95 |
| pop_front | small | 7.77 | 15.6 | 0.50 |
| pop_front | medium | 7.99 | 14.6 | 0.55 |
| pop_front | large | 10.4 | 13.7 | 0.76 |
| pop_back | small | | | pending |
| pop_back | medium | | | pending |
| pop_back | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### FIFO queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| enqueue | small | | | pending |
| enqueue | medium | | | pending |
| enqueue | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| dequeue | small | | | pending |
| dequeue | medium | | | pending |
| dequeue | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Stack

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | | | pending |
| push | medium | | | pending |
| push | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| pop | small | | | pending |
| pop | medium | | | pending |
| pop | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### LIFO queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | | | pending |
| put | medium | | | pending |
| put | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| qsize | small | | | pending |
| qsize | medium | | | pending |
| qsize | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Simple queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | | | pending |
| put | medium | | | pending |
| put | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| qsize | small | | | pending |
| qsize | medium | | | pending |
| qsize | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Priority queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | | | pending |
| put | medium | | | pending |
| put | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| qsize | small | | | pending |
| qsize | medium | | | pending |
| qsize | large | | | pending |
| from_list | small | | | pending |
| from_list | medium | | | pending |
| from_list | large | | | pending |
| to_sorted_list | small | | | pending |
| to_sorted_list | medium | | | pending |
| to_sorted_list | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Binary heap

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | | | pending |
| push | medium | | | pending |
| push | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| from_list | small | | | pending |
| from_list | medium | | | pending |
| from_list | large | | | pending |
| to_sorted_list | small | | | pending |
| to_sorted_list | medium | | | pending |
| to_sorted_list | large | | | pending |
| pop | small | | | pending |
| pop | medium | | | pending |
| pop | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Doubly linked list

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | | | pending |
| push_front | medium | | | pending |
| push_front | large | | | pending |
| push_back | small | | | pending |
| push_back | medium | | | pending |
| push_back | large | | | pending |
| insert_before | small | | | pending |
| insert_before | medium | | | pending |
| insert_before | large | | | pending |
| insert_after | small | | | pending |
| insert_after | medium | | | pending |
| insert_after | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| set | small | | | pending |
| set | medium | | | pending |
| set | large | | | pending |
| next | small | | | pending |
| next | medium | | | pending |
| next | large | | | pending |
| prev | small | | | pending |
| prev | medium | | | pending |
| prev | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| remove | small | | | pending |
| remove | medium | | | pending |
| remove | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### List iterator

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| iter_first | small | | | pending |
| iter_first | medium | | | pending |
| iter_first | large | | | pending |
| iter_last | small | | | pending |
| iter_last | medium | | | pending |
| iter_last | large | | | pending |
| next | small | | | pending |
| next | medium | | | pending |
| next | large | | | pending |
| previous | small | | | pending |
| previous | medium | | | pending |
| previous | large | | | pending |
| set | small | | | pending |
| set | medium | | | pending |
| set | large | | | pending |
| add | small | | | pending |
| add | medium | | | pending |
| add | large | | | pending |
| remove | small | | | pending |
| remove | medium | | | pending |
| remove | large | | | pending |
| has_next | small | | | pending |
| has_next | medium | | | pending |
| has_next | large | | | pending |
| has_previous | small | | | pending |
| has_previous | medium | | | pending |
| has_previous | large | | | pending |
| position | small | | | pending |
| position | medium | | | pending |
| position | large | | | pending |
| finish | small | | | pending |
| finish | medium | | | pending |
| finish | large | | | pending |

### Tree map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| insert | small | | | pending |
| insert | medium | | | pending |
| insert | large | | | pending |
| remove | small | | | pending |
| remove | medium | | | pending |
| remove | large | | | pending |
| lookup | small | | | pending |
| lookup | medium | | | pending |
| lookup | large | | | pending |
| contains | small | | | pending |
| contains | medium | | | pending |
| contains | large | | | pending |
| min | small | | | pending |
| min | medium | | | pending |
| min | large | | | pending |
| max | small | | | pending |
| max | medium | | | pending |
| max | large | | | pending |
| lower_bound | small | | | pending |
| lower_bound | medium | | | pending |
| lower_bound | large | | | pending |
| range | small | | | pending |
| range | medium | | | pending |
| range | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Bitset

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | | | pending |
| set | medium | | | pending |
| set | large | | | pending |
| clear | small | | | pending |
| clear | medium | | | pending |
| clear | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| count | small | | | pending |
| count | medium | | | pending |
| count | large | | | pending |
| length | small | | | pending |
| length | medium | | | pending |
| length | large | | | pending |
| to_list | small | | | pending |
| to_list | medium | | | pending |
| to_list | large | | | pending |
| union | small | | | pending |
| union | medium | | | pending |
| union | large | | | pending |
| intersection | small | | | pending |
| intersection | medium | | | pending |
| intersection | large | | | pending |
| difference | small | | | pending |
| difference | medium | | | pending |
| difference | large | | | pending |
| xor | small | | | pending |
| xor | medium | | | pending |
| xor | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |

### Hash map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | | | pending |
| set | medium | | | pending |
| set | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| has | small | | | pending |
| has | medium | | | pending |
| has | large | | | pending |
| pop | small | | | pending |
| pop | medium | | | pending |
| pop | large | | | pending |
| size | small | | | pending |
| size | medium | | | pending |
| size | large | | | pending |
| keys | small | | | pending |
| keys | medium | | | pending |
| keys | large | | | pending |
| build | small | | | pending |
| build | medium | | | pending |
| build | large | | | pending |

### LRU cache

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| add | small | | | pending |
| add | medium | | | pending |
| add | large | | | pending |
| get | small | | | pending |
| get | medium | | | pending |
| get | large | | | pending |
| peek | small | | | pending |
| peek | medium | | | pending |
| peek | large | | | pending |
| contains | small | | | pending |
| contains | medium | | | pending |
| contains | large | | | pending |
| remove | small | | | pending |
| remove | medium | | | pending |
| remove | large | | | pending |
| purge | small | | | pending |
| purge | medium | | | pending |
| purge | large | | | pending |
| resize | small | | | pending |
| resize | medium | | | pending |
| resize | large | | | pending |
| keys | small | | | pending |
| keys | medium | | | pending |
| keys | large | | | pending |
| len | small | | | pending |
| len | medium | | | pending |
| len | large | | | pending |
| new | small | | | pending |
| new | medium | | | pending |
| new | large | | | pending |
| capacity | small | | | pending |
| capacity | medium | | | pending |
| capacity | large | | | pending |
| set_lifetime | small | | | pending |
| set_lifetime | medium | | | pending |
| set_lifetime | large | | | pending |
| metrics | small | | | pending |
| metrics | medium | | | pending |
| metrics | large | | | pending |
| expiry | small | | | pending |
| expiry | medium | | | pending |
| expiry | large | | | pending |
| remove_seq | small | | | pending |
| remove_seq | medium | | | pending |
| remove_seq | large | | | pending |
| purge_isolated | small | | | pending |
| purge_isolated | medium | | | pending |
| purge_isolated | large | | | pending |
| resize_isolated | small | | | pending |
| resize_isolated | medium | | | pending |
| resize_isolated | large | | | pending |

