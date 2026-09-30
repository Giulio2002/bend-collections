/* AEAD references for benchmarks/bend/suite_aead.bend. BENCH_ALG: 0 ChaCha20-Poly1305
   (Monocypher 4.0.2 crypto_aead_init_ietf + crypto_aead_write), 1 XChaCha20-Poly1305
   (Monocypher crypto_aead_lock), 2 AES-128-GCM and 3 AES-256-GCM (BearSSL br_gcm with the
   constant-time bitsliced br_aes_ct64 CTR and br_ghash_ctmul64; built with -DAES_TABLES, the
   table-based br_aes_big instead). Fixed key and nonce, empty associated data, the key set
   up per message as the Bend API does. BENCH_PARAM 0: encrypt (output ciphertext || tag);
   1: decrypt ciphertexts sealed before the timed region (output the plaintext). */
#include "suite.h"
#include "monocypher.h"
#include "bearssl.h"

#ifdef AES_TABLES
typedef br_aes_big_ctr_keys aes_keys;
#define aes_init br_aes_big_ctr_init
#else
typedef br_aes_ct64_ctr_keys aes_keys;
#define aes_init br_aes_ct64_ctr_init
#endif

static size_t alg, klen, nlen;
static uint8_t key[32], nonce[24];

static void seal(uint8_t *out, const uint8_t *in, size_t n) {
  uint8_t *mac = out + n;
  if (alg == 0) {
    crypto_aead_ctx c; crypto_aead_init_ietf(&c, key, nonce);
    crypto_aead_write(&c, out, mac, 0, 0, in, n);
  } else if (alg == 1) {
    crypto_aead_lock(out, mac, key, nonce, 0, 0, in, n);
  } else {
    aes_keys k; br_gcm_context g;
    aes_init(&k, key, klen);
    br_gcm_init(&g, &k.vtable, br_ghash_ctmul64);
    br_gcm_reset(&g, nonce, 12); br_gcm_flip(&g);
    memmove(out, in, n); br_gcm_run(&g, 1, out, n); br_gcm_get_tag(&g, mac);
  }
}

static int open_(uint8_t *out, const uint8_t *in, size_t n) {
  const uint8_t *mac = in + n;
  if (alg == 0) {
    crypto_aead_ctx c; crypto_aead_init_ietf(&c, key, nonce);
    return crypto_aead_read(&c, out, mac, 0, 0, in, n) == 0;
  } else if (alg == 1) {
    return crypto_aead_unlock(out, mac, key, nonce, 0, 0, in, n) == 0;
  } else {
    aes_keys k; br_gcm_context g;
    aes_init(&k, key, klen);
    br_gcm_init(&g, &k.vtable, br_ghash_ctmul64);
    br_gcm_reset(&g, nonce, 12); br_gcm_flip(&g);
    memmove(out, in, n); br_gcm_run(&g, 0, out, n);
    return br_gcm_check_tag(&g, mac) == 1;
  }
}

int main(void) {
  messages m = load_messages();
  alg = env_num("BENCH_ALG", 0);
  size_t mode = env_num("BENCH_PARAM", 0);
  klen = alg == 2 ? 16 : 32; nlen = alg == 1 ? 24 : 12;
  pattern(key, klen, 7, 1); pattern(nonce, nlen, 3, 5);
  size_t n = m.size, len = n + 16;
  uint8_t *out = malloc(m.count * len + 1);
  double t0, t1;
  if (mode == 0) {
    t0 = now_ms();
    for (size_t i = 0; i < m.count; i++) seal(out + len * i, msg(&m, i), n);
    t1 = now_ms();
    report(t1 - t0, fold_outputs(out, m.count, len));
  } else {
    uint8_t *pt = malloc(m.count * n + 1);
    for (size_t i = 0; i < m.count; i++) seal(out + len * i, msg(&m, i), n);
    int ok = 1;
    t0 = now_ms();
    for (size_t i = 0; i < m.count; i++) ok &= open_(pt + n * i, out + len * i, n);
    t1 = now_ms();
    if (!ok) { fprintf(stderr, "tag rejected\n"); return 1; }
    report(t1 - t0, fold_outputs(pt, m.count, n));
  }
  return 0;
}
