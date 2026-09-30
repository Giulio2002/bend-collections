/* SHA3-256 of every message: XKCP Keccak-p[1600] opt64 (benchmarks/native/xkcp/) with the
   FIPS 202 padding, the reference for benchmarks/bend/suite_sha3_256.bend. */
#include "suite.h"
#include "sha3_ctx.h"
int main(void) {
  messages m = load_messages();
  uint8_t *out = malloc(m.count * 32 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) sha3_256(msg(&m, i), m.size, out + 32 * i);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 32));
  return 0;
}
