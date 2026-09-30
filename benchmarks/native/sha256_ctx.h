/* Portable incremental SHA-256 (FIPS 180-4): the compression function of
   benchmarks/native/sha256.c behind init/update/final, plus HMAC-SHA256
   (RFC 2104) and HKDF-SHA256 (RFC 5869) on top of it. No intrinsics. */
#ifndef SHA256_CTX_H
#define SHA256_CTX_H
#include <stdint.h>
#include <string.h>

static const uint32_t SHA256_K[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};

#define SHA256_ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void sha256_block(uint32_t h[8], const uint8_t *p) {
  uint32_t w[64];
  for (int i = 0; i < 16; i++)
    w[i] = (uint32_t)p[4*i] << 24 | (uint32_t)p[4*i+1] << 16 | (uint32_t)p[4*i+2] << 8 | p[4*i+3];
  for (int i = 16; i < 64; i++) {
    uint32_t s0 = SHA256_ROR(w[i-15], 7) ^ SHA256_ROR(w[i-15], 18) ^ (w[i-15] >> 3);
    uint32_t s1 = SHA256_ROR(w[i-2], 17) ^ SHA256_ROR(w[i-2], 19) ^ (w[i-2] >> 10);
    w[i] = w[i-16] + s0 + w[i-7] + s1;
  }
  uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], k = h[7];
  for (int i = 0; i < 64; i++) {
    uint32_t t1 = k + (SHA256_ROR(e, 6) ^ SHA256_ROR(e, 11) ^ SHA256_ROR(e, 25)) + ((e & f) ^ (~e & g)) + SHA256_K[i] + w[i];
    uint32_t t2 = (SHA256_ROR(a, 2) ^ SHA256_ROR(a, 13) ^ SHA256_ROR(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
    k = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
  }
  h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += k;
}

typedef struct { uint32_t h[8]; uint8_t buf[64]; size_t fill; uint64_t len; } sha256_ctx;

static void sha256_init(sha256_ctx *c) {
  static const uint32_t H0[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
  memcpy(c->h, H0, sizeof H0); c->fill = 0; c->len = 0;
}

static void sha256_update(sha256_ctx *c, const uint8_t *p, size_t n) {
  c->len += n;
  if (c->fill) {
    size_t k = 64 - c->fill < n ? 64 - c->fill : n;
    memcpy(c->buf + c->fill, p, k); c->fill += k; p += k; n -= k;
    if (c->fill < 64) return;
    sha256_block(c->h, c->buf); c->fill = 0;
  }
  for (; n >= 64; p += 64, n -= 64) sha256_block(c->h, p);
  memcpy(c->buf, p, n); c->fill = n;
}

static void sha256_final(sha256_ctx *c, uint8_t out[32]) {
  uint64_t bits = c->len * 8;
  uint8_t pad[72] = {0x80};
  size_t padn = (c->fill < 56 ? 56 : 120) - c->fill;
  for (int j = 0; j < 8; j++) pad[padn + j] = (uint8_t)(bits >> (56 - 8 * j));
  sha256_update(c, pad, padn + 8);
  for (int i = 0; i < 8; i++) {
    out[4*i] = (uint8_t)(c->h[i] >> 24); out[4*i+1] = (uint8_t)(c->h[i] >> 16);
    out[4*i+2] = (uint8_t)(c->h[i] >> 8); out[4*i+3] = (uint8_t)c->h[i];
  }
}

static void sha256_oneshot(const uint8_t *p, size_t n, uint8_t out[32]) {
  sha256_ctx c; sha256_init(&c); sha256_update(&c, p, n); sha256_final(&c, out);
}

/* RFC 2104 */
static void hmac_sha256(const uint8_t *key, size_t klen, const uint8_t *m, size_t n, uint8_t out[32]) {
  uint8_t k[64] = {0}, ipad[64], opad[64], inner[32];
  if (klen > 64) sha256_oneshot(key, klen, k); else memcpy(k, key, klen);
  for (int i = 0; i < 64; i++) { ipad[i] = k[i] ^ 0x36; opad[i] = k[i] ^ 0x5c; }
  sha256_ctx c;
  sha256_init(&c); sha256_update(&c, ipad, 64); sha256_update(&c, m, n); sha256_final(&c, inner);
  sha256_init(&c); sha256_update(&c, opad, 64); sha256_update(&c, inner, 32); sha256_final(&c, out);
}

/* RFC 5869, len <= 255 * 32 */
static void hkdf_sha256(const uint8_t *salt, size_t sn, const uint8_t *ikm, size_t in,
                        const uint8_t *info, size_t fn, uint8_t *out, size_t len) {
  uint8_t prk[32], t[32 + 64 + 1];
  hmac_sha256(salt, sn, ikm, in, prk);
  size_t tl = 0, done = 0;
  for (uint8_t ctr = 1; done < len; ctr++) {
    memcpy(t + tl, info, fn); t[tl + fn] = ctr;
    uint8_t blk[32];
    hmac_sha256(prk, 32, t, tl + fn + 1, blk);
    size_t k = len - done < 32 ? len - done : 32;
    memcpy(out + done, blk, k); done += k;
    memcpy(t, blk, 32); tl = 32;
  }
}
#endif
