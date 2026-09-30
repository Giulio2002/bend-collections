/* The C side of the random group (benchmarks/bend/suite_{chacha8_u64,pcg_u64,uint_below,
   float64,shuffle,crandom}.bend) over gorand.h, Go's math/rand/v2 transcribed. BENCH_OP picks
   the case: 0 chacha8 uint64, 1 PCG uint64, 2 uint_below (BENCH_PARAM 0: n = 1000000007,
   1: n = 2^63 + 1), 3 float64, 4 shuffle, 5 crypto/random bytes (ChaCha8.Read). Draws are
   stored in the timed region and folded after it exactly as suite_randlib.bend does: every
   64-bit value as 8 LE bytes, last draw first; shuffle: the final permutation, 4 LE bytes per
   element, first first; bytes: every byte, last read first. */
#include "suite.h"
#include "gorand.h"

static uint32_t fold_u64s(const uint64_t *x, size_t n) {
  uint32_t c = 0;
  for (size_t i = n; i-- > 0;) for (int j = 0; j < 8; j++) c = c * 31 + (uint8_t)(x[i] >> (8 * j));
  return c;
}

int main(void) {
  size_t op = env_num("BENCH_OP", 0), param = env_num("BENCH_PARAM", 0);
  size_t count = env_num("BENCH_COUNT", 1), size = env_num("BENCH_SIZE", 0);
  uint8_t seed[32]; pattern(seed, 32, 7, 1);
  chacha8_state c8; chacha8_init(&c8, seed);
  double t0, t1; uint32_t sum = 0;
  if (op <= 3) {
    uint64_t *out = malloc(count * 8 + 8);
    if (op == 0) {
      t0 = now_ms();
      for (size_t i = 0; i < count; i++) out[i] = chacha8_uint64(&c8);
      t1 = now_ms();
    } else if (op == 1) {
      go_pcg p; go_pcg_init(&p, 1, 2);
      t0 = now_ms();
      for (size_t i = 0; i < count; i++) out[i] = go_pcg_uint64(&p);
      t1 = now_ms();
    } else if (op == 2) {
      uint64_t n = param ? (1ull << 63) + 1 : 1000000007ull;
      t0 = now_ms();
      for (size_t i = 0; i < count; i++) out[i] = chacha8_uint64n(&c8, n);
      t1 = now_ms();
    } else {
      double *d = (double *)out;
      t0 = now_ms();
      for (size_t i = 0; i < count; i++) d[i] = chacha8_float64(&c8);
      t1 = now_ms();
      /* the binary64 bit pattern, as the Bend side folds F64.Bits */
      for (size_t i = 0; i < count; i++) { uint64_t b; memcpy(&b, &d[i], 8); out[i] = b; }
    }
    sum = fold_u64s(out, count);
  } else if (op == 4) {
    uint32_t *xs = malloc(size * 4 + 4);
    for (size_t i = 0; i < size; i++) xs[i] = (uint32_t)i;
    t0 = now_ms();
    for (size_t k = 0; k < count; k++) chacha8_shuffle_u32(&c8, xs, size);
    t1 = now_ms();
    for (size_t i = 0; i < size; i++) for (int j = 0; j < 4; j++) sum = sum * 31 + (uint8_t)(xs[i] >> (8 * j));
  } else {
    go_chacha8 g; go_chacha8_init(&g, seed);
    uint8_t *out = malloc(count * size + 1);
    t0 = now_ms();
    for (size_t k = 0; k < count; k++) go_chacha8_read(&g, out + k * size, size);
    t1 = now_ms();
    sum = fold_outputs(out, count, size);
  }
  report(t1 - t0, sum);
  return 0;
}
