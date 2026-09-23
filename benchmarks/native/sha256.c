/* Portable C SHA-256 (FIPS 180-4), the reference for benchmarks/bend/sha256.bend.
   Same protocol: SHA_BENCH_INPUT names a file, SHA_BENCH_SIZE the message size;
   the file is cut into messages of that size before timing, every message is
   hashed inside the timed region, then BENCH_MS and every digest (hex) are
   printed. Straight-line rounds, no intrinsics or assembly. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static const uint32_t K[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};

#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void block(uint32_t h[8], const uint8_t *p) {
  uint32_t w[64];
  for (int i = 0; i < 16; i++)
    w[i] = (uint32_t)p[4*i] << 24 | (uint32_t)p[4*i+1] << 16 | (uint32_t)p[4*i+2] << 8 | p[4*i+3];
  for (int i = 16; i < 64; i++) {
    uint32_t s0 = ROR(w[i-15], 7) ^ ROR(w[i-15], 18) ^ (w[i-15] >> 3);
    uint32_t s1 = ROR(w[i-2], 17) ^ ROR(w[i-2], 19) ^ (w[i-2] >> 10);
    w[i] = w[i-16] + s0 + w[i-7] + s1;
  }
  uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], k = h[7];
  for (int i = 0; i < 64; i++) {
    uint32_t t1 = k + (ROR(e, 6) ^ ROR(e, 11) ^ ROR(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i];
    uint32_t t2 = (ROR(a, 2) ^ ROR(a, 13) ^ ROR(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
    k = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
  }
  h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += k;
}

static void sha256(const uint8_t *m, size_t n, uint32_t h[8]) {
  static const uint32_t H0[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
  memcpy(h, H0, sizeof H0);
  size_t i = 0;
  for (; i + 64 <= n; i += 64) block(h, m + i);
  uint8_t tail[128] = {0};
  size_t r = n - i;
  memcpy(tail, m + i, r);
  tail[r] = 0x80;
  size_t len = r + 9 <= 64 ? 64 : 128;
  uint64_t bits = (uint64_t)n * 8;
  for (int j = 0; j < 8; j++) tail[len - 1 - j] = (uint8_t)(bits >> (8 * j));
  block(h, tail);
  if (len == 128) block(h, tail + 64);
}

static double now_ms(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec * 1e-6; }

int main(void) {
  const char *path = getenv("SHA_BENCH_INPUT"), *st = getenv("SHA_BENCH_SIZE");
  if (!path || !st) return 1;
  size_t size = strtoull(st, 0, 10);
  FILE *f = fopen(path, "rb");
  if (!f) return 1;
  fseek(f, 0, SEEK_END); size_t n = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  uint8_t *data = malloc(n ? n : 1);
  if (fread(data, 1, n, f) != n) return 1;
  fclose(f);
  size_t count = size ? (n + size - 1) / size : 1;
  if (count == 0) count = 1;
  uint32_t (*out)[8] = malloc(count * sizeof *out);
  double t0 = now_ms();
  for (size_t i = 0; i < count; i++) {
    size_t off = i * size, len = off + size <= n ? size : n - off;
    sha256(data + off, len, out[i]);
  }
  double t1 = now_ms();
  printf("BENCH_MS=%.3f\n", t1 - t0);
  for (size_t i = count; i-- > 0;) {   /* the Bend driver prints the last message first */
    for (int j = 0; j < 8; j++) printf("%08x", out[i][j]);
    printf("\n");
  }
  free(out); free(data);
  return 0;
}
