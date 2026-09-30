/* Incremental SHA3-256 (FIPS 202) over XKCP's Keccak-p[1600] (benchmarks/native/xkcp/):
   rate 136 bytes, domain padding 0x06 ... 0x80. */
#ifndef SHA3_CTX_H
#define SHA3_CTX_H
#include <stddef.h>
#include "KeccakP-1600-SnP.h"
typedef struct { KeccakP1600_state s; unsigned int fill; } sha3_ctx;
static void sha3_init(sha3_ctx *c) { KeccakP1600_Initialize(&c->s); c->fill = 0; }
static void sha3_update(sha3_ctx *c, const unsigned char *p, size_t n) {
  if (c->fill) {
    unsigned int k = 136 - c->fill < n ? 136 - c->fill : (unsigned int)n;
    KeccakP1600_AddBytes(&c->s, p, c->fill, k); c->fill += k; p += k; n -= k;
    if (c->fill < 136) return;
    KeccakP1600_Permute_24rounds(&c->s); c->fill = 0;
  }
  for (; n >= 136; p += 136, n -= 136) { KeccakP1600_AddBytes(&c->s, p, 0, 136); KeccakP1600_Permute_24rounds(&c->s); }
  KeccakP1600_AddBytes(&c->s, p, 0, (unsigned int)n); c->fill = (unsigned int)n;
}
static void sha3_final(sha3_ctx *c, unsigned char out[32]) {
  KeccakP1600_AddByte(&c->s, 0x06, c->fill); KeccakP1600_AddByte(&c->s, 0x80, 135);
  KeccakP1600_Permute_24rounds(&c->s); KeccakP1600_ExtractBytes(&c->s, out, 0, 32);
}
static void sha3_256(const unsigned char *p, size_t n, unsigned char out[32]) {
  sha3_ctx c; sha3_init(&c); sha3_update(&c, p, n); sha3_final(&c, out);
}
#endif
