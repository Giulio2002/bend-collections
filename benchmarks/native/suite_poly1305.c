/* The Poly1305 tag of every message under a fixed key with Monocypher 4.0.2
   crypto_poly1305; the reference for benchmarks/bend/suite_poly1305.bend. */
#include "suite.h"
#include "monocypher.h"
int main(void) {
  messages m = load_messages();
  uint8_t key[32]; pattern(key, 32, 7, 1);
  uint8_t *out = malloc(m.count * 16 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) crypto_poly1305(out + 16 * i, msg(&m, i), m.size, key);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 16));
  return 0;
}
