/* Ed25519 key generation: every 32-byte message is a seed, the output the public key.
   Monocypher 4.0.2 crypto_ed25519_key_pair (it wipes its seed argument, so each seed is
   copied first), the reference for benchmarks/bend/suite_ed25519_keygen.bend. */
#include "suite.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  uint8_t *out = malloc(m.count * 32 + 1);
  /* one pass over the messages takes well under a millisecond, so the pass is repeated
     until 50 ms have passed and BENCH_MS is the mean time of one pass */
  double t0 = now_ms(), t1;
  size_t passes = 0;
  do {
    for (size_t i = 0; i < m.count; i++) {
      uint8_t seed[32], sk[64];
      memcpy(seed, msg(&m, i), 32);
      crypto_ed25519_key_pair(sk, out + 32 * i, seed);
    }
    passes++;
  } while ((t1 = now_ms()) - t0 < 50);
  report((t1 - t0) / passes, fold_outputs(out, m.count, 32));
  return 0;
}
