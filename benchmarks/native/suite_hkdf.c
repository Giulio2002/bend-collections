/* HKDF-SHA256 (RFC 5869 over sha256_ctx.h): every message is the input keying material,
   fixed 32-byte salt and 16-byte info, BENCH_PARAM output bytes; the reference for
   benchmarks/bend/suite_hkdf.bend. */
#include "suite.h"
#include "sha256_ctx.h"
int main(void) {
  messages m = load_messages();
  size_t len = env_num("BENCH_PARAM", 32);
  uint8_t salt[32], info[16]; pattern(salt, 32, 5, 3); pattern(info, 16, 3, 11);
  uint8_t *out = malloc(m.count * len + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) hkdf_sha256(salt, 32, msg(&m, i), m.size, info, 16, out + len * i, len);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, len));
  return 0;
}
