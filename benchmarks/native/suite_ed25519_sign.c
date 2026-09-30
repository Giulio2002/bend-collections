/* Ed25519 signing of every message under the fixed seed pattern(32, 13, 7). Monocypher
   4.0.2 crypto_ed25519_sign with the 64-byte secret key (seed || public key) made once
   before the timed region (the Bend API re-derives the public key per call), the reference
   for benchmarks/bend/suite_ed25519_sign.bend. */
#include "suite.h"
#include "monocypher-ed25519.h"
int main(void) {
  messages m = load_messages();
  uint8_t seed[32], sk[64], pk[32]; pattern(seed, 32, 13, 7); crypto_ed25519_key_pair(sk, pk, seed);
  uint8_t *out = malloc(m.count * 64 + 1);
  /* one pass over the messages takes well under a millisecond, so the pass is repeated
     until 50 ms have passed and BENCH_MS is the mean time of one pass */
  double t0 = now_ms(), t1;
  size_t passes = 0;
  do {
    for (size_t i = 0; i < m.count; i++) crypto_ed25519_sign(out + 64 * i, sk, msg(&m, i), m.size);
    passes++;
  } while ((t1 = now_ms()) - t0 < 50);
  report((t1 - t0) / passes, fold_outputs(out, m.count, 64));
  return 0;
}
