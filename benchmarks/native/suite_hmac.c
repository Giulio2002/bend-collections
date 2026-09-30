/* HMAC-SHA256 (RFC 2104 over the portable SHA-256 of sha256_ctx.h) of every message under a
   fixed 32-byte key, the reference for benchmarks/bend/suite_hmac.bend. */
#include "suite.h"
#include "sha256_ctx.h"
int main(void) {
  messages m = load_messages();
  uint8_t key[32]; pattern(key, 32, 7, 1);
  uint8_t *out = malloc(m.count * 32 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) hmac_sha256(key, 32, msg(&m, i), m.size, out + 32 * i);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 32));
  return 0;
}
