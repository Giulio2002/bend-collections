/* SHA-512 of every message: Monocypher 4.0.2 crypto_sha512 (benchmarks/native/monocypher/),
   the reference for benchmarks/bend/suite_sha512.bend. */
#include "suite.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  uint8_t *out = malloc(m.count * 64 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) crypto_sha512(out + 64 * i, msg(&m, i), m.size);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 64));
  return 0;
}
