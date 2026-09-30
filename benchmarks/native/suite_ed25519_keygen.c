/* Ed25519 key generation: every 32-byte message is a seed, the output the public key.
   Monocypher 4.0.2 crypto_ed25519_key_pair (it wipes its seed argument, so each seed is
   copied first), the reference for benchmarks/bend/suite_ed25519_keygen.bend. */
#include "suite.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  uint8_t *out = malloc(m.count * 32 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) {
    uint8_t seed[32], sk[64];
    memcpy(seed, msg(&m, i), 32);
    crypto_ed25519_key_pair(sk, out + 32 * i, seed);
  }
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 32));
  return 0;
}
