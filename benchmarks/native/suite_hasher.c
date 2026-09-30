/* Incremental hashing, the reference for benchmarks/bend/suite_hasher.bend. BENCH_ALGO: 0
   SHA-256 (sha256_ctx.h, portable FIPS 180-4), 1 SHA-512 (Monocypher 4.0.2
   crypto_sha512_init/update/final), 2 SHA3-256 (sha3_ctx.h over XKCP). BENCH_PARAM 0: the
   one-shot function; k > 0: init, update in k-byte chunks, final. */
#include "suite.h"
#include "sha256_ctx.h"
#include "sha3_ctx.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  size_t chunk = env_num("BENCH_PARAM", 0), algo = env_num("BENCH_ALGO", 0);
  size_t len = algo == 1 ? 64 : 32;
  uint8_t *out = malloc(m.count * len + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) {
    const uint8_t *p = msg(&m, i);
    uint8_t *o = out + len * i;
    if (!chunk) {
      if (algo == 0) sha256_oneshot(p, m.size, o);
      else if (algo == 1) crypto_sha512(o, p, m.size);
      else sha3_256(p, m.size, o);
    } else if (algo == 0) {
      sha256_ctx c; sha256_init(&c);
      for (size_t off = 0; off < m.size; off += chunk) sha256_update(&c, p + off, m.size - off < chunk ? m.size - off : chunk);
      sha256_final(&c, o);
    } else if (algo == 1) {
      crypto_sha512_ctx c; crypto_sha512_init(&c);
      for (size_t off = 0; off < m.size; off += chunk) crypto_sha512_update(&c, p + off, m.size - off < chunk ? m.size - off : chunk);
      crypto_sha512_final(&c, o);
    } else {
      sha3_ctx c; sha3_init(&c);
      for (size_t off = 0; off < m.size; off += chunk) sha3_update(&c, p + off, m.size - off < chunk ? m.size - off : chunk);
      sha3_final(&c, o);
    }
  }
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, len));
  return 0;
}
