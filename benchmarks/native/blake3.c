/* Official BLAKE3 C reference (benchmarks/native/blake/, CC0), portable build:
   cc -O3 -march=native -DBLAKE3_NO_SSE2 -DBLAKE3_NO_SSE41 -DBLAKE3_NO_AVX2
      -DBLAKE3_NO_AVX512 -DBLAKE3_USE_NEON=0 -Ibenchmarks/native/blake
      benchmarks/native/blake3.c benchmarks/native/blake/blake3.c
      benchmarks/native/blake/blake3_dispatch.c benchmarks/native/blake/blake3_portable.c
   The reference for benchmarks/bend/blake3.bend: same input words, same
   per-hash copy of the input, same checksum (sum of the first little-endian
   digest word). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "blake3.h"
static void hash(const unsigned char *p, size_t n, unsigned char out[32]) {
  blake3_hasher h; blake3_hasher_init(&h); blake3_hasher_update(&h, p, n); blake3_hasher_finalize(&h, out, 32);
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
int main(void) {
  size_t n = strtoull(getenv("BLAKE_SIZE"), 0, 10), depth = strtoull(getenv("BLAKE_DEPTH"), 0, 10), count = strtoull(getenv("BLAKE_COUNT"), 0, 10);
  size_t cap = ((size_t)1 << depth) * 4;
  unsigned char *data = malloc(cap), *copy = malloc(cap);
  for (size_t i = 0; i < cap / 4; i++) { uint32_t w = (uint32_t)i * 2654435761u + 42; for (int j = 0; j < 4; j++) data[i * 4 + j] = w >> (j * 8); }
  unsigned char out[32]; uint32_t sum = 0; double start = now();
  for (size_t i = 0; i < count; i++) {
    memcpy(copy, data, cap); hash(copy, n, out);
    sum += (uint32_t)out[0] | ((uint32_t)out[1] << 8) | ((uint32_t)out[2] << 16) | ((uint32_t)out[3] << 24);
  }
  printf("BENCH_MS=%.6f\n%u\n", (now() - start) * 1000, sum);
  for (int j = 0; j < 32; j++) printf("%02x", out[j]);
  printf("\n"); free(copy); free(data); return 0;
}
