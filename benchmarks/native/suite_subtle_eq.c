/* Constant-time equality (lengths public, then OR of the XOR of every byte pair, no early
   exit), the reference for benchmarks/bend/suite_subtle_eq.bend: every message against an
   equal copy. */
#include "suite.h"
static int ct_eq(const uint8_t *a, size_t an, const uint8_t *b, size_t bn) {
  if (an != bn) return 0;
  uint8_t acc = 0;
  for (size_t i = 0; i < an; i++) acc |= a[i] ^ b[i];
  return acc == 0;
}
int main(void) {
  messages m = load_messages();
  uint8_t *copy = malloc(m.count * m.size + 1), *out = malloc(m.count + 1);
  memcpy(copy, m.data, m.count * m.size);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++) out[i] = (uint8_t)ct_eq(msg(&m, i), m.size, copy + i * m.size, m.size);
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 1));
  return 0;
}
