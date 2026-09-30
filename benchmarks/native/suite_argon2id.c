/* Argon2id (RFC 9106): every 16-byte message is a password; fixed 16-byte salt
   pattern(16, 11, 7), no secret or associated data, one lane, 32-byte tag. BENCH_PARAM 0:
   m = 64 KiB, t = 3; 1: m = 19456 KiB, t = 2. The official P-H-C reference, portable ref.c
   (benchmarks/native/argon2/), the reference for benchmarks/bend/suite_argon2id.bend. */
#include "suite.h"
#include "argon2.h"
int main(void) {
  messages m = load_messages();
  size_t param = env_num("BENCH_PARAM", 0);
  uint32_t t = param ? 2 : 3, mem = param ? 19456 : 64;
  uint8_t salt[16]; pattern(salt, 16, 11, 7);
  uint8_t *out = malloc(m.count * 32 + 1);
  double t0 = now_ms();
  for (size_t i = 0; i < m.count; i++)
    if (argon2id_hash_raw(t, mem, 1, msg(&m, i), m.size, salt, 16, out + 32 * i, 32) != ARGON2_OK) return 1;
  double t1 = now_ms();
  report(t1 - t0, fold_outputs(out, m.count, 32));
  return 0;
}
