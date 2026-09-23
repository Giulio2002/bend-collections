# Benchmarks

Every row runs the same algorithm in Bend (native C backend, one thread) and in C
(`-O3 -march=native`), with identical inputs, and the two results must agree
(a checksum of every result, or the full digests). **Ratio = Bend time / C time**:
below 1 Bend is faster.

Machine: arm64, macOS-15.6-arm64-arm-64bit-Mach-O. Measured while other work was running on the machine, so
absolute times are noisy; each sample alternates Bend and C under the same load,
so the ratios are the meaningful column.

Reproduce:

```sh
python3 benchmarks/full_sweep.py --report build/bench/full.json   # containers
python3 benchmarks/crypto.py --report build/bench/crypto.json      # hashes
python3 benchmarks/maps/compare.py --report build/bench/maps.json  # HashMap vs Base.Map
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

Each row measures one public operation at three structure sizes. The time of
an operation is the difference between two regions that run 2k and k of them
(build, settle and teardown cancel); removals are measured in a restoring pair
with the insertion that puts the element back. Nanoseconds per operation,
median of six samples. A sample in which other load interrupted a region (A - B
negative or under the timing minimum) is re-taken, both sides together, up to
four times; failed rows are re-measured with `full_sweep.py --retry-failed`.
See `benchmarks/run.py` for the method.

† quick sampling (`BENCH_QUICK=1`): a 10 ms instead of 50 ms minimum difference and
three samples instead of six, several rows in parallel. Expect about ±10% on
those ratios; the unmarked rows use the full method.

### Dynamic array

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 25.9 | 10.7 | 2.42 |
| push | medium | 25.0 | 10.1 | 2.48 |
| push | large | 46.8 | 22.3 | 2.09 |
| get | small | 22.8 | 3.63 | 6.27 |
| get | medium | 22.0 | 3.27 | 6.72 |
| get | large | 21.2 | 1.41 | 15.04 |
| set | small | 5.90 | 3.44 | 1.72 |
| set | medium | 2.72 | 2.01 | 1.36 |
| set | large | 4.33 | 2.17 | 1.99 |
| length | small | 1.62 | 4.75 | 0.34 |
| length | medium | 1.65 | 5.37 | 0.31 |
| length | large | 1.63 | 4.89 | 0.33 |
| capacity | small | 1.54 | 4.02 | 0.38 |
| capacity | medium | 1.53 | 5.32 | 0.29 |
| capacity | large | 1.42 | 4.33 | 0.33 |
| reserve | small | 1.73 | 1.78 | 0.97 |
| reserve | medium | 1.80 | 1.54 | 1.16 |
| reserve | large | 2.54 | 2.99 | 0.85 |
| to_list | small | 329 | 152 | 2.17 |
| to_list | medium | 20429 | 10592 | 1.93 |
| to_list | large | 933333 | 650377 | 1.44 |
| clear | small | 342 | 13.3 | 25.74 |
| clear | medium | 19400 | 257 | 75.55 |
| clear | large | 1354000 | 17795 | 76.09 |
| pop | small | 12.4 | 6.49 | 1.91 |
| pop | medium | 8.63 | 6.52 | 1.32 |
| pop | large | 8.36 | 6.73 | 1.24 |
| new | small | 12.7 | 3.79 | 3.35 |
| new | medium | 10.0 | 3.60 | 2.79 |
| new | large | 18.5 | 4.00 | 4.63 |

### Deque

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | 35.6 | 33.7 | 1.06 |
| push_front | medium | 26.9 | 29.4 | 0.91 |
| push_front | large | 20.1 | 35.3 | 0.57 |
| push_back | small | 28.6 | 22.7 | 1.26 |
| push_back | medium | 26.7 | 30.8 | 0.87 |
| push_back | large | 19.2 | 21.6 | 0.89 |
| peek_front | small | 5.27 | 4.83 | 1.09 |
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
| pop_back | small | 8.48 | 15.3 | 0.56 |
| pop_back | medium | 8.24 | 17.1 | 0.48 |
| pop_back | large | 12.2 | 17.3 | 0.70 |
| new | small | 1.36 | 1.97 | 0.69 |
| new | medium | 1.37 | 1.90 | 0.72 |
| new | large | 1.42 | 2.11 | 0.67 |

### FIFO queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| enqueue | small | 13.1 | 16.3 | 0.80 |
| enqueue | medium | 13.4 | 21.3 | 0.63 |
| enqueue | large | 13.7 | 16.4 | 0.83 |
| peek | small | 5.74 | 5.33 | 1.08 |
| peek | medium | 4.50 | 4.46 | 1.01 |
| peek | large | 3.25 | 3.45 | 0.94 |
| length | small | 1.01 | 2.86 | 0.35 |
| length | medium | 1.05 | 3.09 | 0.34 |
| length | large | 1.02 | 2.91 | 0.35 |
| to_list | small | 1027 | 1080 | 0.95 |
| to_list | medium | 79500 | 78383 | 1.01 |
| to_list | large | 4480000 | 6853410 | 0.65 |
| dequeue | small | 22.1 | 15.9 | 1.39 |
| dequeue | medium | 16.4 | 21.9 | 0.75 |
| dequeue | large | 28.0 | 45.0 | 0.62 |
| new | small | 1.39 | 2.17 | 0.64 |
| new | medium | 1.40 | 1.90 | 0.74 |
| new | large | 1.35 | 1.87 | 0.72 |

### Stack

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 12.4 | 24.8 | 0.50 |
| push | medium | 11.5 | 28.5 | 0.40 |
| push | large | 13.0 | 25.8 | 0.50 |
| peek | small | 1.91 | 1.62 | 1.18 |
| peek | medium | 2.18 | 1.73 | 1.26 |
| peek | large | 2.22 | 1.47 | 1.51 |
| length | small | 1.28 | 3.63 | 0.35 |
| length | medium | 1.25 | 3.60 | 0.35 |
| length | large | 1.33 | 3.86 | 0.35 |
| to_list | small | 586 | 29.4 | 19.98 |
| to_list | medium | 47167 | 4074 | 11.58 |
| to_list | large | 2790000 | 457680 | 6.10 |
| pop | small | 3.42 | 15.9 | 0.21 |
| pop | medium | 3.91 | 16.1 | 0.24 |
| pop | large | 3.26 | 17.2 | 0.19 |
| new | small | 1.34 | 1.54 | 0.87 |
| new | medium | 1.34 | 1.76 | 0.76 |
| new | large | 1.33 | 1.62 | 0.82 |

### Simple queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | 17.5 | 23.0 | 0.76 † |
| put | medium | 18.8 | 32.1 | 0.58 † |
| put | large | 16.2 | 48.1 | 0.34 † |
| peek | small | 6.64 | 6.76 | 0.98 † |
| peek | medium | 8.12 | 4.62 | 1.76 † |
| peek | large | 13.3 | 4.81 | 2.77 † |
| qsize | small | 1.41 | 4.08 | 0.34 † |
| qsize | medium | 1.33 | 4.43 | 0.30 † |
| qsize | large | 1.46 | 6.54 | 0.22 † |
| to_list | small | 1200 | 1576 | 0.76 † |
| to_list | medium | 80000 | 113022 | 0.71 † |
| to_list | large | 5700000 | 7305740 | 0.78 † |
| get | small | 21.7 | 15.8 | 1.37 † |
| get | medium | 17.5 | 30.4 | 0.58 † |
| get | large | 32.5 | 66.1 | 0.49 † |
| new | small | 1.35 | 3.37 | 0.40 † |
| new | medium | 2.08 | 5.37 | 0.39 † |
| new | large | 1.82 | 2.95 | 0.62 † |

### Priority queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | 47.5 | 18.4 | 2.58 † |
| put | medium | 35.6 | 16.2 | 2.20 † |
| put | large | 77.2 | 16.7 | 4.62 † |
| peek | small | 1.56 | 2.18 | 0.72 † |
| peek | medium | 1.46 | 1.84 | 0.80 † |
| peek | large | | | not timeable |
| qsize | small | 1.33 | 4.02 | 0.33 † |
| qsize | medium | 1.64 | 4.16 | 0.39 † |
| qsize | large | 2.03 | 4.24 | 0.48 † |
| from_list | small | 200 | 68.0 | 2.94 † |
| from_list | medium | 200 | 84.3 | 2.37 † |
| from_list | large | 200 | 81.4 | 2.46 † |
| to_sorted_list | small | 3667 | 728 | 5.04 † |
| to_sorted_list | medium | 530000 | 108630 | 4.88 † |
| to_sorted_list | large | 30600000 | 5391400 | 5.68 † |
| get | small | 105 | 21.7 | 4.84 † |
| get | medium | 200 | 48.1 | 4.16 † |
| get | large | 425 | 66.8 | 6.36 † |
| new | small | 10.9 | 2.83 | 3.86 † |
| new | medium | 8.75 | 3.50 | 2.50 † |
| new | large | 12.5 | 3.55 | 3.52 † |

### Binary heap

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push | small | 30.7 | 13.7 | 2.24 |
| push | medium | 26.8 | 12.4 | 2.16 |
| push | large | 70.7 | 17.1 | 4.12 |
| peek | small | 1.43 | 1.51 | 0.95 |
| peek | medium | 1.38 | 1.99 | 0.69 |
| peek | large | 1.75 | 1.63 | 1.08 |
| length | small | 1.44 | 4.01 | 0.36 |
| length | medium | 1.40 | 3.90 | 0.36 |
| length | large | 1.40 | 3.86 | 0.36 |
| from_list | small | 191 | 85.0 | 2.24 |
| from_list | medium | 166 | 73.8 | 2.25 |
| from_list | large | 213 | 76.8 | 2.78 |
| to_sorted_list | small | 3827 | 685 | 5.59 |
| to_sorted_list | medium | 349000 | 95718 | 3.65 |
| to_sorted_list | large | 26700000 | 4638400 | 5.76 |
| pop | small | 92.9 | 20.3 | 4.57 |
| pop | medium | 204 | 40.2 | 5.06 |
| pop | large | 286 | 65.9 | 4.33 |
| new | small | 8.91 | 3.20 | 2.79 |
| new | medium | 10.6 | 3.70 | 2.87 |
| new | large | 11.6 | 3.18 | 3.66 |

### Doubly linked list

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| push_front | small | 25.9 | 9.99 | 2.59 |
| push_front | medium | 19.8 | 7.97 | 2.48 |
| push_front | large | 22.3 | 9.72 | 2.29 |
| push_back | small | 18.9 | 6.28 | 3.01 |
| push_back | medium | 26.6 | 9.28 | 2.86 |
| push_back | large | 25.7 | 8.62 | 2.99 |
| insert_before | small | 30.7 | 8.78 | 3.50 |
| insert_before | medium | 28.0 | 7.69 | 3.64 |
| insert_before | large | 44.3 | 10.3 | 4.31 |
| insert_after | small | 29.6 | 9.27 | 3.20 |
| insert_after | medium | 33.4 | 9.26 | 3.61 |
| insert_after | large | 45.3 | 15.0 | 3.02 |
| get | small | 17.3 | 2.24 | 7.73 |
| get | medium | 17.7 | 2.99 | 5.91 |
| get | large | 38.6 | 2.97 | 12.98 |
| set | small | 3.00 | 1.92 | 1.56 |
| set | medium | 3.74 | 2.03 | 1.84 |
| set | large | 3.00 | 2.11 | 1.42 |
| next | small | 4.68 | 3.10 | 1.51 |
| next | medium | 3.97 | 2.61 | 1.52 |
| next | large | 5.47 | 3.21 | 1.70 |
| prev | small | 5.63 | 2.70 | 2.08 |
| prev | medium | 5.16 | 2.28 | 2.26 |
| prev | large | 5.26 | 3.22 | 1.63 |
| length | small | 1.04 | 2.94 | 0.35 |
| length | medium | 1.23 | 3.52 | 0.35 |
| length | large | 1.35 | 4.27 | 0.32 |
| to_list | small | 355 | 182 | 1.95 |
| to_list | medium | 7034 | 6321 | 1.11 |
| to_list | large | 213690 | 131173 | 1.63 |
| remove | small | 9.78 | 13.2 | 0.74 |
| remove | medium | 10.1 | 9.56 | 1.06 |
| remove | large | 14.2 | 10.8 | 1.31 |
| new | small | 16.6 | 3.47 | 4.79 |
| new | medium | 26.2 | 3.52 | 7.43 |
| new | large | 19.7 | 4.03 | 4.89 |

### List iterator

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| iter_first | small | 6.88 | 4.96 | 1.39 † |
| iter_first | medium | 7.42 | 4.96 | 1.50 † |
| iter_first | large | 7.42 | 5.08 | 1.46 † |
| iter_last | small | 6.88 | 5.77 | 1.19 † |
| iter_last | medium | 6.64 | 5.18 | 1.28 † |
| iter_last | large | 6.77 | 5.32 | 1.27 † |
| next | small | 12.5 | 3.00 | 4.16 † |
| next | medium | 10.4 | 4.92 | 2.12 † |
| next | large | 11.9 | 3.17 | 3.76 † |
| previous | small | 10.0 | 3.67 | 2.72 † |
| previous | medium | 10.9 | 2.70 | 4.05 † |
| previous | large | 10.9 | 2.90 | 3.77 † |
| set | small | 1.80 | 1.95 | 0.92 † |
| set | medium | 1.51 | 1.77 | 0.85 † |
| set | large | 1.46 | 1.53 | 0.96 † |
| add | small | 27.5 | 8.88 | 3.10 † |
| add | medium | 25.0 | 8.91 | 2.81 † |
| add | large | 37.5 | 8.48 | 4.42 † |
| remove | small | 26.2 | 9.76 | 2.69 † |
| remove | medium | 26.6 | 10.7 | 2.48 † |
| remove | large | 31.2 | 13.1 | 2.39 † |
| has_next | small | 1.33 | 1.91 | 0.70 † |
| has_next | medium | 1.46 | 1.70 | 0.86 † |
| has_next | large | 1.42 | 1.73 | 0.82 † |
| has_previous | small | 1.33 | 1.62 | 0.82 † |
| has_previous | medium | 1.32 | 1.41 | 0.93 † |
| has_previous | large | 1.27 | 1.37 | 0.93 † |
| position | small | 1.25 | 1.87 | 0.67 † |
| position | medium | 1.51 | 1.99 | 0.76 † |
| position | large | 1.27 | 1.85 | 0.69 † |
| finish | small | 7.81 | 5.09 | 1.53 † |
| finish | medium | 7.03 | 5.01 | 1.40 † |
| finish | large | 7.29 | 5.50 | 1.33 † |

### Tree map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| insert | small | 194 | 37.3 | 5.21 |
| insert | medium | 352 | 93.5 | 3.77 |
| insert | large | 3300 | 337 | 9.78 † |
| remove | small | 1645 | 84.2 | 19.53 |
| remove | medium | 1960 | 166 | 11.77 |
| remove | large | 4975 | 654 | 7.61 |
| lookup | small | 145 | 23.5 | 6.15 |
| lookup | medium | 315 | 55.5 | 5.67 |
| lookup | large | 575 | 95.2 | 6.04 |
| contains | small | 90.8 | 18.3 | 4.95 |
| contains | medium | 205 | 38.8 | 5.28 |
| contains | large | 450 | 85.9 | 5.24 |
| min | small | 16.2 | 1.50 | 10.81 |
| min | medium | 16.1 | 3.62 | 4.45 |
| min | large | 15.8 | 5.69 | 2.77 |
| max | small | 16.3 | 1.49 | 10.93 |
| max | medium | 16.2 | 2.36 | 6.84 |
| max | large | 19.5 | 4.96 | 3.93 |
| lower_bound | small | 169 | 20.3 | 8.34 |
| lower_bound | medium | 391 | 45.6 | 8.59 |
| lower_bound | large | 1500 | 125 | 12.04 † |
| range | small | 938 | 49.8 | 18.83 † |
| range | medium | 53333 | 1513 | 35.24 † |
| range | large | 3500000 | 124450 | 28.12 † |
| to_list | small | 3750 | 69.5 | 53.96 † |
| to_list | medium | 300000 | 5490 | 54.64 † |
| to_list | large | | | not timeable |
| length | small | 1.30 | 3.87 | 0.34 † |
| length | medium | 1.33 | 3.59 | 0.37 † |
| length | large | | | not timeable |
| new | small | 23.6 | 3.73 | 6.35 † |
| new | medium | 22.5 | 3.24 | 6.95 † |
| new | large | | | not timeable |

### Bitset

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 2.66 | 1.87 | 1.42 † |
| set | medium | 2.03 | 1.71 | 1.19 † |
| set | large | 1.21 | 2.01 | 0.60 † |
| clear | small | 2.03 | 2.17 | 0.93 † |
| clear | medium | 2.11 | 1.56 | 1.35 † |
| clear | large | 1.88 | 1.65 | 1.14 † |
| get | small | 2.19 | 1.86 | 1.17 † |
| get | medium | 2.27 | 2.15 | 1.06 † |
| get | large | 2.71 | 2.30 | 1.18 † |
| count | small | 17.5 | 5.80 | 3.02 † |
| count | medium | 550 | 298 | 1.85 † |
| count | large | 22000 | 17442 | 1.26 † |
| length | small | 1.33 | 3.64 | 0.36 † |
| length | medium | 1.25 | 3.80 | 0.33 † |
| length | large | 1.33 | 3.61 | 0.37 † |
| to_list | small | 300 | 88.7 | 3.38 † |
| to_list | medium | 13000 | 5255 | 2.47 † |
| to_list | large | 1660000 | 374800 | 4.43 † |
| union | small | 2.50 | 0.90 | 2.78 † |
| union | medium | 78.1 | 65.2 | 1.20 † |
| union | large | 5667 | 5676 | 1.00 † |
| intersection | small | 3.75 | 2.86 | 1.31 † |
| intersection | medium | 87.5 | 74.2 | 1.18 † |
| intersection | large | 4875 | 4796 | 1.02 † |
| difference | small | 2.29 | 3.93 | 0.58 † |
| difference | medium | 84.4 | 97.0 | 0.87 † |
| difference | large | 4250 | 4622 | 0.92 † |
| xor | small | 1.88 | 1.83 | 1.02 † |
| xor | medium | 81.2 | 86.3 | 0.94 † |
| xor | large | 4500 | 4970 | 0.91 † |
| new | small | 6.09 | 13.2 | 0.46 † |
| new | medium | 7.19 | 17.9 | 0.40 † |
| new | large | 5.94 | 18.8 | 0.32 † |

### Hash map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 16.9 | 3.49 | 4.84 † |
| set | medium | 22.5 | 3.87 | 5.81 † |
| set | large | 181 | 51.4 | 3.53 † |
| get | small | 36.2 | 1.36 | 26.70 † |
| get | medium | 51.2 | 2.64 | 19.42 † |
| get | large | 388 | 39.0 | 9.92 † |
| has | small | 22.5 | 2.26 | 9.96 † |
| has | medium | 22.5 | 3.24 | 6.95 † |
| has | large | | | not timeable |
| pop | small | 55.0 | 4.43 | 12.41 † |
| pop | medium | 55.0 | 10.7 | 5.14 † |
| pop | large | 292 | 26.2 | 11.14 † |
| size | small | 1.88 | 4.56 | 0.41 † |
| size | medium | 1.35 | 3.30 | 0.41 † |
| size | large | 1.98 | 3.72 | 0.53 † |
| keys | small | 550 | 41.3 | 13.32 † |
| keys | medium | 28000 | 4310 | 6.50 † |
| keys | large | 475000 | 36250 | 13.10 † |
| build | small | 2667 | 595 | 4.48 † |
| build | medium | 262500 | 38188 | 6.87 † |
| build | large | 2062500 | 210500 | 9.80 † |

### LRU cache

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| add | small | 22.5 | 12.0 | 1.88 † |
| add | medium | 43.8 | 11.7 | 3.75 † |
| add | large | 575 | 17.5 | 32.86 † |
| get | small | 27.5 | 17.3 | 1.59 † |
| get | medium | 30.0 | 23.7 | 1.26 † |
| get | large | 279 | 196 | 1.43 † |
| peek | small | 30.0 | 19.1 | 1.57 † |
| peek | medium | | | not timeable |
| peek | large | | | not timeable |
| contains | small | 20.8 | 5.03 | 4.14 † |
| contains | medium | 26.2 | 4.92 | 5.34 † |
| contains | large | 166 | 42.5 | 3.90 † |
| remove | small | 80.0 | 19.2 | 4.16 † |
| remove | medium | 80.0 | 32.5 | 2.46 † |
| remove | large | 375 | 120 | 3.13 † |
| purge | small | 2667 | 424 | 6.30 † |
| purge | medium | 225000 | 65512 | 3.43 † |
| purge | large | 25000000 | 3409000 | 7.33 † |
| resize | small | 3833 | 495 | 7.75 † |
| resize | medium | 225000 | 45188 | 4.98 † |
| resize | large | 58500000 | 3968250 | 14.74 † |
| keys | small | 1400 | 241 | 5.81 † |
| keys | medium | 80000 | 19214 | 4.16 † |
| keys | large | 575000 | 152950 | 3.76 † |
| len | small | 1.56 | 4.48 | 0.35 † |
| len | medium | 1.41 | 3.73 | 0.38 † |
| len | large | 12.5 | 7.13 | 1.75 † |
| new | small | 65.0 | 24.3 | 2.67 † |
| new | medium | 45.0 | 33.0 | 1.36 † |
| new | large | | | not timeable |
| capacity | small | 1.48 | 4.97 | 0.30 † |
| capacity | medium | 1.64 | 5.11 | 0.32 † |
| capacity | large | | | not timeable |
| set_lifetime | small | 8.44 | 9.61 | 0.88 † |
| set_lifetime | medium | 5.94 | 8.24 | 0.72 † |
| set_lifetime | large | 8.59 | 9.69 | 0.89 † |
| metrics | small | 18.4 | 10.7 | 1.72 † |
| metrics | medium | 15.0 | 9.59 | 1.56 † |
| metrics | large | | | not timeable |
| expiry | small | 66.7 | 13.8 | 4.84 † |
| expiry | medium | 55.0 | 17.9 | 3.07 † |
| expiry | large | 400 | 120 | 3.35 † |
| remove_seq | small | 30.5 | 6.04 | 5.06 † |
| remove_seq | medium | 53.4 | 10.7 | 5.01 † |
| remove_seq | large | 275 | 121 | 2.28 † |
| purge_isolated | small | | | not timeable |
| purge_isolated | medium | 30556 | 12800 | 2.39 † |
| purge_isolated | large | | | not timeable |
| resize_isolated | small | 2031 | 215 | 9.46 † |
| resize_isolated | medium | | | not timeable |
| resize_isolated | large | 460938 | 14309 | 32.21 † |

## Hash map vs Base.Map

Both sides are Bend: the hash map of `src/containers/hash_table.bend` against
the standard library's `Base.Map` (a crit-bit tree over String keys), on the
same operations, String keys and inputs, with identical checksums. Same
differential method as the containers. **Ratio = HashMap time / Base.Map time**:
below 1 the hash map is faster. `Base.Map.size` walks the tree, so the
hash map's O(1) size is compared against an O(n) walk. See
`benchmarks/maps/compare.py`.

| Operation | Size | HashMap (ns) | Base.Map (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | 64 | 22.7 | 420 | 0.05 |
| set | 4096 | 23.4 | 939 | 0.02 |
| set | 262144 | 100 | 1388 | 0.07 † |
| get | 64 | 26.4 | 181 | 0.15 |
| get | 4096 | 28.9 | 485 | 0.06 |
| get | 262144 | 75.5 | 1843 | 0.04 |
| has | 64 | 16.9 | 181 | 0.09 |
| has | 4096 | 19.8 | 450 | 0.04 |
| has | 262144 | 14.8 | 1145 | 0.01 † |
| pop | 64 | 40.0 | 720 | 0.06 † |
| pop | 4096 | 51.7 | 893 | 0.06 † |
| pop | 262144 | 225 | 1583 | 0.14 † |
| size | 64 | 1.41 | 319 | 0.00 † |
| size | 4096 | | | not timeable |
| size | 262144 | | | not timeable |
| keys | 64 | 400 | 1350 | 0.30 † |
| keys | 4096 | 34000 | 110000 | 0.31 † |
| keys | 32768 | 400000 | 925000 | 0.43 † |
| build | 64 | 3000 | 17167 | 0.17 † |
| build | 4096 | 256250 | 1150000 | 0.22 † |
| build | 32768 | 1500000 | 8625000 | 0.17 † |

