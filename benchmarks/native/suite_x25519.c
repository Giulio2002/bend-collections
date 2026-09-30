/* X25519 shared secret: every 32-byte message is a secret key, the peer public key is
   X25519(pattern(32, 9, 5), 9) made before the timed region. Monocypher 4.0.2 crypto_x25519
   (benchmarks/native/monocypher/), the reference for benchmarks/bend/suite_x25519.bend. */
#include "suite.h"
#include "monocypher.h"
int main(void) {
  messages m = load_messages();
  uint8_t peer_sk[32], pk[32]; pattern(peer_sk, 32, 9, 5); crypto_x25519_public_key(pk, peer_sk);
  uint8_t *out = malloc(m.count * 32 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) crypto_x25519(out + 32 * i, msg(&m, i), pk);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 32));
  return 0;
}
