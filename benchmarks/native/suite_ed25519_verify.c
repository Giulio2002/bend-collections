/* Ed25519 verification: every message is signed under the fixed seed pattern(32, 13, 7)
   before the timed region, then every signature is checked (output 1 when valid).
   Monocypher 4.0.2 crypto_ed25519_check, the reference for
   benchmarks/bend/suite_ed25519_verify.bend. */
#include "suite.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  uint8_t seed[32], sk[64], pk[32]; pattern(seed, 32, 13, 7); crypto_ed25519_key_pair(sk, pk, seed);
  uint8_t *sig = malloc(m.count * 64 + 1), *out = malloc(m.count + 1);
  for (size_t i = 0; i < m.count; i++) crypto_ed25519_sign(sig + 64 * i, sk, msg(&m, i), m.size);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) out[i] = crypto_ed25519_check(sig + 64 * i, pk, msg(&m, i), m.size) == 0;
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 1));
  return 0;
}
