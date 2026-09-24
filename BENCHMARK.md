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

† quick sampling (`BENCH_QUICK=1`): a 20 ms instead of 50 ms minimum difference and
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
| clear | small | 0.98 | 1.50 | 0.65 † |
| clear | medium | 1.03 | 1.52 | 0.68 † |
| clear | large | 1.17 | 1.53 | 0.77 † |
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
| put | small | 7.81 | 11.1 | 0.70 † |
| put | medium | 7.90 | 10.1 | 0.78 † |
| put | large | 8.11 | 10.4 | 0.78 † |
| peek | small | 3.20 | 3.45 | 0.93 † |
| peek | medium | 3.33 | 3.39 | 0.98 † |
| peek | large | 3.87 | 3.50 | 1.11 † |
| qsize | small | 0.97 | 2.67 | 0.36 † |
| qsize | medium | 1.00 | 2.64 | 0.38 † |
| qsize | large | 0.99 | 2.66 | 0.37 † |
| to_list | small | 683 | 674 | 1.01 † |
| to_list | medium | 48000 | 42648 | 1.13 † |
| to_list | large | 3100000 | 2968860 | 1.04 † |
| get | small | 13.4 | 9.41 | 1.43 † |
| get | medium | 8.06 | 9.45 | 0.85 † |
| get | large | 12.2 | 11.2 | 1.09 † |
| new | small | 0.97 | 1.22 | 0.79 † |
| new | medium | 0.97 | 1.23 | 0.79 † |
| new | large | 0.99 | 1.23 | 0.80 † |

### Priority queue

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| put | small | 18.8 | 9.34 | 2.01 † |
| put | medium | 18.8 | 9.18 | 2.04 † |
| put | large | 23.8 | 8.99 | 2.65 † |
| peek | small | 1.00 | 1.00 | 1.00 † |
| peek | medium | 0.99 | 1.00 | 0.99 † |
| peek | large | 1.01 | 0.99 | 1.02 † |
| qsize | small | 0.96 | 2.62 | 0.37 † |
| qsize | medium | 0.95 | 2.62 | 0.36 † |
| qsize | large | 0.94 | 2.66 | 0.35 † |
| from_list | small | 120 | 53.1 | 2.26 † |
| from_list | medium | 117 | 53.4 | 2.19 † |
| from_list | large | 123 | 53.7 | 2.28 † |
| to_sorted_list | small | 2250 | 476 | 4.73 † |
| to_sorted_list | medium | 320000 | 55480 | 5.77 † |
| to_sorted_list | large | 16400000 | 3261800 | 5.03 † |
| get | small | 70.0 | 13.7 | 5.12 † |
| get | medium | 130 | 31.0 | 4.19 † |
| get | large | 188 | 46.6 | 4.03 † |
| new | small | 5.65 | 2.33 | 2.42 † |
| new | medium | 5.48 | 2.32 | 2.37 † |
| new | large | 7.74 | 2.55 | 3.03 † |

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
| iter_first | small | 4.84 | 3.26 | 1.48 † |
| iter_first | medium | 4.56 | 3.20 | 1.42 † |
| iter_first | large | 4.59 | 3.20 | 1.43 † |
| iter_last | small | 4.41 | 3.34 | 1.32 † |
| iter_last | medium | 4.35 | 3.34 | 1.30 † |
| iter_last | large | 4.40 | 3.37 | 1.31 † |
| next | small | 6.67 | 1.76 | 3.79 † |
| next | medium | 6.45 | 1.77 | 3.64 † |
| next | large | 6.53 | 1.81 | 3.62 † |
| previous | small | 5.97 | 2.02 | 2.95 † |
| previous | medium | 5.76 | 1.88 | 3.06 † |
| previous | large | 6.05 | 1.86 | 3.26 † |
| set | small | 1.02 | 0.99 | 1.02 † |
| set | medium | 0.99 | 1.03 | 0.96 † |
| set | large | 1.00 | 1.03 | 0.98 † |
| add | small | 15.6 | 5.65 | 2.77 † |
| add | medium | 15.7 | 5.68 | 2.77 † |
| add | large | 15.7 | 5.81 | 2.70 † |
| remove | small | 15.5 | 5.70 | 2.72 † |
| remove | medium | 15.3 | 5.68 | 2.70 † |
| remove | large | 15.7 | 5.68 | 2.76 † |
| has_next | small | 0.99 | 1.00 | 0.99 † |
| has_next | medium | 0.95 | 1.02 | 0.94 † |
| has_next | large | 0.95 | 0.99 | 0.96 † |
| has_previous | small | 0.94 | 0.99 | 0.95 † |
| has_previous | medium | 0.93 | 0.99 | 0.94 † |
| has_previous | large | 0.98 | 1.01 | 0.97 † |
| position | small | 0.97 | 1.00 | 0.97 † |
| position | medium | 0.93 | 0.98 | 0.95 † |
| position | large | 0.93 | 1.01 | 0.92 † |
| finish | small | 4.61 | 3.19 | 1.44 † |
| finish | medium | 4.69 | 3.13 | 1.50 † |
| finish | large | 4.64 | 3.18 | 1.46 † |

### Tree map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| insert | small | 73.5 | 23.7 | 3.10 |
| insert | medium | 144 | 60.2 | 2.39 |
| insert | large | 271 | 142 | 1.91 |
| remove | small | 353 | 53.4 | 6.61 |
| remove | medium | 540 | 117 | 4.63 |
| remove | large | 757 | 221 | 3.43 |
| lookup | small | 67.1 | 15.7 | 4.28 |
| lookup | medium | 136 | 35.9 | 3.79 |
| lookup | large | 252 | 79.9 | 3.16 |
| contains | small | 56.3 | 17.5 | 3.21 |
| contains | medium | 121 | 37.0 | 3.27 |
| contains | large | 226 | 80.6 | 2.81 |
| min | small | 14.2 | 1.49 | 9.57 |
| min | medium | 14.2 | 3.84 | 3.70 |
| min | large | 14.3 | 5.89 | 2.42 |
| max | small | 14.3 | 1.49 | 9.60 |
| max | medium | 14.3 | 2.42 | 5.91 |
| max | large | 14.2 | 4.83 | 2.95 |
| lower_bound | small | 71.3 | 16.9 | 4.21 |
| lower_bound | medium | 143 | 37.4 | 3.82 |
| lower_bound | large | 268 | 83.8 | 3.19 |
| range | small | 221 | 29.9 | 7.38 |
| range | medium | 13810 | 798 | 17.31 |
| range | large | 140000 | 6802 | 20.58 |
| to_list | small | 995 | 45.3 | 21.96 |
| to_list | medium | 80769 | 3028 | 26.68 |
| to_list | large | 3533333 | 211917 | 16.67 |
| length | small | 0.91 | 2.61 | 0.35 |
| length | medium | 0.91 | 2.62 | 0.35 |
| length | large | 0.91 | 2.62 | 0.35 |
| new | small | 29.2 | 2.28 | 12.81 |
| new | medium | 28.8 | 2.28 | 12.63 |
| new | large | 26.1 | 2.32 | 11.23 |

### Bitset

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 1.45 | 1.28 | 1.13 † |
| set | medium | 1.29 | 1.15 | 1.12 † |
| set | large | 1.34 | 1.15 | 1.17 † |
| clear | small | 1.45 | 1.26 | 1.15 † |
| clear | medium | 1.31 | 1.15 | 1.14 † |
| clear | large | 1.32 | 1.14 | 1.15 † |
| get | small | 1.61 | 1.32 | 1.22 † |
| get | medium | 1.48 | 1.19 | 1.25 † |
| get | large | 1.47 | 1.18 | 1.24 † |
| count | small | 11.6 | 3.91 | 2.95 † |
| count | medium | 309 | 186 | 1.67 † |
| count | large | 15500 | 11911 | 1.30 † |
| length | small | 0.99 | 2.74 | 0.36 † |
| length | medium | 0.94 | 2.62 | 0.36 † |
| length | large | 0.95 | 3.03 | 0.31 † |
| to_list | small | 155 | 61.1 | 2.53 † |
| to_list | medium | 8250 | 3798 | 2.17 † |
| to_list | large | 840000 | 242880 | 3.46 † |
| union | small | 1.31 | 1.17 | 1.12 † |
| union | medium | 50.0 | 48.7 | 1.03 † |
| union | large | 2818 | 2884 | 0.98 † |
| intersection | small | 1.23 | 1.02 | 1.20 † |
| intersection | medium | 49.2 | 48.2 | 1.02 † |
| intersection | large | 2839 | 2884 | 0.98 † |
| difference | small | 1.25 | 1.10 | 1.14 † |
| difference | medium | 50.0 | 48.5 | 1.03 † |
| difference | large | 2774 | 2929 | 0.95 † |
| xor | small | 1.31 | 1.06 | 1.23 † |
| xor | medium | 51.6 | 42.0 | 1.23 † |
| xor | large | 2710 | 2895 | 0.94 † |
| new | small | 2.42 | 8.96 | 0.27 † |
| new | medium | 2.50 | 9.29 | 0.27 † |
| new | large | 2.42 | 9.24 | 0.26 † |

### Hash map

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| set | small | 9.68 | 2.24 | 4.32 † |
| set | medium | 10.6 | 2.24 | 4.74 † |
| set | large | 14.3 | 2.74 | 5.21 † |
| get | small | 22.5 | 1.50 | 15.04 † |
| get | medium | 22.6 | 1.35 | 16.67 † |
| get | large | 35.5 | 1.83 | 19.36 † |
| has | small | 10.3 | 1.26 | 8.21 † |
| has | medium | 8.75 | 1.27 | 6.91 † |
| has | large | 10.4 | 1.44 | 7.19 † |
| pop | small | 25.5 | 2.75 | 9.24 † |
| pop | medium | 29.7 | 2.76 | 10.74 † |
| pop | large | 36.7 | 3.89 | 9.43 † |
| size | small | 0.94 | 2.28 | 0.41 † |
| size | medium | 0.92 | 2.28 | 0.40 † |
| size | large | 0.94 | 2.26 | 0.41 † |
| keys | small | 258 | 54.0 | 4.79 † |
| keys | medium | 15000 | 2898 | 5.18 † |
| keys | large | 193750 | 22412 | 8.64 † |
| build | small | 1719 | 416 | 4.14 † |
| build | medium | 118750 | 20810 | 5.71 † |
| build | large | 1142857 | 172071 | 6.64 † |

### LRU cache

| Operation | Size | Bend (ns) | C (ns) | Ratio |
|---|---:|---:|---:|---:|
| add | small | 13.8 | 9.13 | 1.51 † |
| add | medium | 22.9 | 10.3 | 2.21 † |
| add | large | | | not timeable |
| get | small | 15.8 | 10.5 | 1.50 † |
| get | medium | 16.8 | 11.8 | 1.42 † |
| get | large | 36.4 | 62.6 | 0.58 † |
| peek | small | 15.6 | 9.60 | 1.63 † |
| peek | medium | 15.5 | 9.55 | 1.62 † |
| peek | large | 77.7 | 33.3 | 2.33 † |
| contains | small | 11.0 | 1.41 | 7.76 † |
| contains | medium | 10.6 | 1.27 | 8.40 † |
| contains | large | 22.3 | 2.51 | 8.88 † |
| remove | small | 40.0 | 12.5 | 3.19 † |
| remove | medium | 45.0 | 11.3 | 3.98 † |
| remove | large | 93.8 | 33.4 | 2.80 † |
| purge | small | 1227 | 332 | 3.69 † |
| purge | medium | 81818 | 20625 | 3.97 † |
| purge | large | 7750000 | 1449500 | 5.35 † |
| resize | small | 977 | 223 | 4.38 † |
| resize | medium | 84375 | 20244 | 4.17 † |
| resize | large | 8250000 | 1711750 | 4.82 † |
| keys | small | 633 | 85.8 | 7.38 † |
| keys | medium | 38000 | 11023 | 3.45 † |
| keys | large | 291667 | 88750 | 3.29 † |
| len | small | 1.02 | 2.70 | 0.38 † |
| len | medium | 1.08 | 2.67 | 0.40 † |
| len | large | 1.04 | 2.72 | 0.38 † |
| new | small | 18.4 | 10.0 | 1.84 † |
| new | medium | 17.7 | 10.1 | 1.75 † |
| new | large | 23.6 | 9.65 | 2.45 † |
| capacity | small | 0.99 | 2.74 | 0.36 † |
| capacity | medium | 0.97 | 2.68 | 0.36 † |
| capacity | large | 0.95 | 2.69 | 0.35 † |
| set_lifetime | small | 3.36 | 6.06 | 0.55 † |
| set_lifetime | medium | 3.36 | 6.16 | 0.55 † |
| set_lifetime | large | 3.45 | 6.35 | 0.54 † |
| metrics | small | 9.89 | 7.39 | 1.34 † |
| metrics | medium | 9.38 | 6.43 | 1.46 † |
| metrics | large | 9.84 | 6.39 | 1.54 † |
| expiry | small | 34.5 | 8.31 | 4.16 † |
| expiry | medium | 35.0 | 8.67 | 4.04 † |
| expiry | large | 49.6 | 21.3 | 2.33 † |
| remove_seq | small | 16.1 | 3.16 | 5.10 † |
| remove_seq | medium | 18.2 | 6.20 | 2.94 † |
| remove_seq | large | 31.0 | 12.7 | 2.43 † |
| purge_isolated | small | 141 | 49.8 | 2.83 † |
| purge_isolated | medium | 7635 | 1187 | 6.43 † |
| purge_isolated | large | | | not timeable |
| resize_isolated | small | 469 | 82.8 | 5.66 † |
| resize_isolated | medium | 10254 | 4732 | 2.17 † |
| resize_isolated | large | 60484 | 29536 | 2.05 † |

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

