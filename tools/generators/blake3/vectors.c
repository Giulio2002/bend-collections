/* Expected BLAKE3 digests for tests/crypto/blake/blake3/main.bend, from the
   official C reference (benchmarks/native/blake/, portable build).
   mode 0: official input pattern byte i = i % 251.
   mode 1: packed words w_i = i*2654435761 + seed, little-endian bytes. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "blake3.h"
int main(int argc, char **argv) {
  int mode = atoi(argv[1]); size_t n = strtoull(argv[2], 0, 10); uint32_t seed = argc > 3 ? (uint32_t)strtoul(argv[3], 0, 10) : 0;
  unsigned char *p = malloc(n + 4);
  for (size_t i = 0; i < n; i++) {
    if (mode == 0) p[i] = (unsigned char)(i % 251);
    else { uint32_t w = (uint32_t)(i / 4) * 2654435761u + seed; p[i] = (unsigned char)(w >> (8 * (i % 4))); }
  }
  blake3_hasher h; blake3_hasher_init(&h); blake3_hasher_update(&h, p, n);
  uint8_t out[32]; blake3_hasher_finalize(&h, out, 32);
  for (int i = 0; i < 32; i++) printf("%02x", out[i]); printf("\n");
  return 0;
}
