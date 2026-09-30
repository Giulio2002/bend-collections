/* Go's math/rand/v2 generators, transcribed to C for benchmarks/crypto_suite.py's random group.

   Transcribed from Go 1.23 (BSD-3-Clause, benchmarks/native/gorand-LICENSE):
     src/internal/chacha8rand/chacha8.go          State: Init, Next, Refill (ctrInc 4, ctrMax 16,
                                                  chunk 32, reseed 4)
     src/internal/chacha8rand/chacha8_generic.go  setup, block_generic (4 interleaved ChaCha8
                                                  blocks; only b4..b11 get the key added back)
     src/math/rand/v2/chacha8.go                  ChaCha8.Uint64, ChaCha8.Read (readBuf/readLen)
     src/math/rand/v2/pcg.go                      PCG.next (128-bit LCG), PCG.Uint64 (DXSM)
     src/math/rand/v2/rand.go                     uint64n (64-bit path), Float64, Shuffle
   The C2SP chacha8rand specification describes the same stream. Checked against Go's vectors
   (chacha8_test.go chacha8output and chacha8hash, pcg_test.go TestPCG). Plain portable C, no
   SIMD (Go's own amd64/arm64 builds use a SIMD block function). */
#ifndef GORAND_H
#define GORAND_H
#include <stdint.h>
#include <string.h>

/* ---- internal/chacha8rand ---- */
typedef struct { uint64_t seed[4]; uint64_t buf[32]; uint32_t c, i, n; } chacha8_state;

#define C8_ROTL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))
#define C8_QR(a, b, c, d) \
  a += b; d ^= a; d = C8_ROTL(d, 16); c += d; b ^= c; b = C8_ROTL(b, 12); \
  a += b; d ^= a; d = C8_ROTL(d, 8);  c += d; b ^= c; b = C8_ROTL(b, 7);

static void chacha8_block(const uint64_t seed[4], uint64_t buf[32], uint32_t counter) {
  uint32_t b[16][4];
  for (int i = 0; i < 4; i++) {                       /* setup */
    b[0][i] = 0x61707865; b[1][i] = 0x3320646e; b[2][i] = 0x79622d32; b[3][i] = 0x6b206574;
    for (int k = 0; k < 4; k++) { b[4 + 2*k][i] = (uint32_t)seed[k]; b[5 + 2*k][i] = (uint32_t)(seed[k] >> 32); }
    b[12][i] = counter + (uint32_t)i; b[13][i] = 0; b[14][i] = 0; b[15][i] = 0;
  }
  for (int i = 0; i < 4; i++) {                       /* block_generic */
    uint32_t x0 = b[0][i], x1 = b[1][i], x2 = b[2][i], x3 = b[3][i], x4 = b[4][i], x5 = b[5][i],
             x6 = b[6][i], x7 = b[7][i], x8 = b[8][i], x9 = b[9][i], x10 = b[10][i], x11 = b[11][i],
             x12 = b[12][i], x13 = b[13][i], x14 = b[14][i], x15 = b[15][i];
    for (int round = 0; round < 4; round++) {
      C8_QR(x0, x4, x8, x12) C8_QR(x1, x5, x9, x13) C8_QR(x2, x6, x10, x14) C8_QR(x3, x7, x11, x15)
      C8_QR(x0, x5, x10, x15) C8_QR(x1, x6, x11, x12) C8_QR(x2, x7, x8, x13) C8_QR(x3, x4, x9, x14)
    }
    b[0][i] = x0; b[1][i] = x1; b[2][i] = x2; b[3][i] = x3;
    b[4][i] += x4; b[5][i] += x5; b[6][i] += x6; b[7][i] += x7;
    b[8][i] += x8; b[9][i] += x9; b[10][i] += x10; b[11][i] += x11;
    b[12][i] = x12; b[13][i] = x13; b[14][i] = x14; b[15][i] = x15;
  }
  const uint32_t *w = &b[0][0];                        /* buf as the uint64 view of b */
  for (int k = 0; k < 32; k++) buf[k] = (uint64_t)w[2*k] | (uint64_t)w[2*k + 1] << 32;
}

static void chacha8_init(chacha8_state *s, const uint8_t seed[32]) {
  for (int k = 0; k < 4; k++) {
    uint64_t v = 0;
    for (int j = 7; j >= 0; j--) v = v << 8 | seed[8*k + j];
    s->seed[k] = v;
  }
  chacha8_block(s->seed, s->buf, 0);
  s->c = 0; s->i = 0; s->n = 32;
}

static void chacha8_refill(chacha8_state *s) {
  s->c += 4;
  if (s->c == 16) {
    for (int k = 0; k < 4; k++) s->seed[k] = s->buf[32 - 4 + k];
    s->c = 0;
  }
  chacha8_block(s->seed, s->buf, s->c);
  s->i = 0;
  s->n = s->c == 16 - 4 ? 32 - 4 : 32;
}

/* math/rand/v2 ChaCha8.Uint64 */
static inline uint64_t chacha8_uint64(chacha8_state *s) {
  for (;;) {
    if (s->i < s->n) return s->buf[s->i++ & 31];
    chacha8_refill(s);
  }
}

/* math/rand/v2 ChaCha8 with Read's partial-word buffer */
typedef struct { chacha8_state st; uint8_t read_buf[8]; int read_len; } go_chacha8;

static void go_chacha8_init(go_chacha8 *c, const uint8_t seed[32]) { chacha8_init(&c->st, seed); c->read_len = 0; }

static void go_chacha8_read(go_chacha8 *c, uint8_t *p, size_t n) {
  if (c->read_len > 0) {
    size_t k = (size_t)c->read_len < n ? (size_t)c->read_len : n;
    memcpy(p, c->read_buf + 8 - c->read_len, k);
    c->read_len -= (int)k; p += k; n -= k;
  }
  for (; n >= 8; p += 8, n -= 8) {
    uint64_t x = chacha8_uint64(&c->st);
    for (int j = 0; j < 8; j++) p[j] = (uint8_t)(x >> (8 * j));
  }
  if (n > 0) {
    uint64_t x = chacha8_uint64(&c->st);
    for (int j = 0; j < 8; j++) c->read_buf[j] = (uint8_t)(x >> (8 * j));
    memcpy(p, c->read_buf, n);
    c->read_len = 8 - (int)n;
  }
}

/* ---- math/rand/v2 PCG ---- */
typedef struct { uint64_t hi, lo; } go_pcg;

static void go_pcg_init(go_pcg *p, uint64_t seed1, uint64_t seed2) { p->hi = seed1; p->lo = seed2; }

static inline uint64_t go_pcg_uint64(go_pcg *p) {
  const uint64_t mulHi = 2549297995355413924ull, mulLo = 4865540595714422341ull,
                 incHi = 6364136223846793005ull, incLo = 1442695040888963407ull;
  /* state = state * mul + inc */
  unsigned __int128 m = (unsigned __int128)p->lo * mulLo;
  uint64_t hi = (uint64_t)(m >> 64), lo = (uint64_t)m;
  hi += p->hi * mulLo + p->lo * mulHi;
  unsigned __int128 s = ((unsigned __int128)hi << 64 | lo) + ((unsigned __int128)incHi << 64 | incLo);
  p->lo = lo = (uint64_t)s; p->hi = hi = (uint64_t)(s >> 64);
  /* DXSM */
  const uint64_t cheapMul = 0xda942042e4dd58b5ull;
  hi ^= hi >> 32;
  hi *= cheapMul;
  hi ^= hi >> (3 * 16);
  hi *= (lo | 1);
  return hi;
}

/* ---- math/rand/v2 Rand over a source; SRC_UINT64(ctx) is the Source ---- */
#define GO_UINT64N(name, T, SRC)                                                     \
  static inline uint64_t name(T *r, uint64_t n) {                                    \
    if ((n & (n - 1)) == 0) return SRC(r) & (n - 1);                                 \
    unsigned __int128 m = (unsigned __int128)SRC(r) * n;                             \
    uint64_t hi = (uint64_t)(m >> 64), lo = (uint64_t)m;                             \
    if (lo < n) {                                                                    \
      uint64_t thresh = -n % n;                                                      \
      while (lo < thresh) { m = (unsigned __int128)SRC(r) * n; hi = (uint64_t)(m >> 64); lo = (uint64_t)m; } \
    }                                                                                \
    return hi;                                                                       \
  }
GO_UINT64N(chacha8_uint64n, chacha8_state, chacha8_uint64)

static inline double chacha8_float64(chacha8_state *r) {
  return (double)(chacha8_uint64(r) << 11 >> 11) / (double)(1ull << 53);
}

/* Shuffle of n uint32 elements with swap(i, j) = exchange */
static void chacha8_shuffle_u32(chacha8_state *r, uint32_t *xs, size_t n) {
  for (size_t i = n; i-- > 1;) {
    size_t j = (size_t)chacha8_uint64n(r, (uint64_t)i + 1);
    uint32_t t = xs[i]; xs[i] = xs[j]; xs[j] = t;
  }
}
#endif
