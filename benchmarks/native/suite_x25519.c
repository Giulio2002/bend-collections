/* X25519 shared secret: every 32-byte message is a secret key, the peer public key is
   X25519(pattern(32, 9, 5), 9) made before the timed region. Monocypher 4.0.2 crypto_x25519
   (benchmarks/native/monocypher/), the reference for benchmarks/bend/suite_x25519.bend. */
#include "suite.h"
#include "monocypher.h"
int main(void) {
  messages m = load_messages();
  uint8_t peer_sk[32], pk[32]; pattern(peer_sk, 32, 9, 5); crypto_x25519_public_key(pk, peer_sk);
  uint8_t *out = malloc(m.count * 32 + 1);
  /* one pass over the messages takes well under a millisecond, so the pass is repeated
     until 50 ms have passed and BENCH_MS is the mean time of one pass */
  double t0 = now_ms(), t1;
  size_t passes = 0;
  do {
    for (size_t i = 0; i < m.count; i++) crypto_x25519(out + 32 * i, msg(&m, i), pk);
    passes++;
  } while ((t1 = now_ms()) - t0 < 50);
  report((t1 - t0) / passes, fold_outputs(out, m.count, 32));
  return 0;
}
