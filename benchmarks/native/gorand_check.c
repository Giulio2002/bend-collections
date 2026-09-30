/* Checks gorand.h against Go's published vectors (tools/check_random.py, from Go's
   chacha8_test.go and pcg_test.go): prints the first 372 ChaCha8 outputs for the seed
   "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456", 20 NewPCG(1, 2) outputs and 2976 bytes of
   ChaCha8.Read in chunks of 1, 7, 64 and 100 bytes (hex); benchmarks/suite_cases_random.py
   compares them (python3 benchmarks/suite_cases_random.py --check <binary>). */
#include <stdio.h>
#include "gorand.h"
int main(void) {
  const uint8_t *seed = (const uint8_t *)"ABCDEFGHIJKLMNOPQRSTUVWXYZ123456";
  chacha8_state s; chacha8_init(&s, seed);
  for (int i = 0; i < 372; i++) printf("c8 %016llx\n", (unsigned long long)chacha8_uint64(&s));
  go_pcg p; go_pcg_init(&p, 1, 2);
  for (int i = 0; i < 20; i++) printf("pcg %016llx\n", (unsigned long long)go_pcg_uint64(&p));
  int chunks[] = {1, 7, 64, 100};
  for (int c = 0; c < 4; c++) {
    go_chacha8 g; go_chacha8_init(&g, seed);
    uint8_t buf[2976];
    for (int off = 0; off < 2976; off += chunks[c]) {
      int k = 2976 - off < chunks[c] ? 2976 - off : chunks[c];
      go_chacha8_read(&g, buf + off, (size_t)k);
    }
    printf("read%d ", chunks[c]);
    for (int i = 0; i < 2976; i++) printf("%02x", buf[i]);
    printf("\n");
  }
  return 0;
}
