/* ChaCha20 (RFC 8439) encryption of every message with Monocypher 4.0.2
   crypto_chacha20_ietf: fixed key and nonce, initial counter 1; the reference for
   benchmarks/bend/suite_chacha20.bend. */
#include "suite.h"
#include "monocypher.h"
int main(void) {
  messages m = load_messages();
  uint8_t key[32], nonce[12]; pattern(key, 32, 7, 1); pattern(nonce, 12, 3, 5);
  uint8_t *out = malloc(m.count * m.size + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) crypto_chacha20_ietf(out + m.size * i, msg(&m, i), m.size, key, nonce, 1);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, m.size));
  return 0;
}
