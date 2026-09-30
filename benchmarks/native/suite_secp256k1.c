/* secp256k1 on 32-byte messages under the fixed secret key pattern(32, 17, 3), the
   reference for benchmarks/bend/suite_secp256k1.bend: libsecp256k1 v0.6.0
   (benchmarks/native/secp256k1/). BENCH_PARAM: 0 ECDSA sign (RFC 6979 default nonce, low s,
   serialized r || s || recid), 1 ECDSA verify (compressed key parsed and signature parsed
   inside the timed region, as the Bend API takes bytes), 2 public key recovery (65-byte
   uncompressed output), 3 BIP-340 sign (aux = pattern(32, 19, 1)), 4 BIP-340 verify.
   Signatures for 1, 2 and 4 are made before the timed region. */
#include "suite.h"
#include "secp256k1.h"
#include "secp256k1_recovery.h"
#include "secp256k1_extrakeys.h"
#include "secp256k1_schnorrsig.h"
int main(void) {
  messages m = load_messages();
  size_t op = env_num("BENCH_PARAM", 0);
  secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  uint8_t sk[32], aux[32], pk33[33], xpk32[32]; pattern(sk, 32, 17, 3); pattern(aux, 32, 19, 1);
  secp256k1_pubkey pub; secp256k1_keypair kp; secp256k1_xonly_pubkey xpub;
  size_t l = 33;
  if (!secp256k1_ec_pubkey_create(ctx, &pub, sk) || !secp256k1_keypair_create(ctx, &kp, sk)) return 1;
  secp256k1_ec_pubkey_serialize(ctx, pk33, &l, &pub, SECP256K1_EC_COMPRESSED);
  secp256k1_keypair_xonly_pub(ctx, &xpub, NULL, &kp);
  secp256k1_xonly_pubkey_serialize(ctx, xpk32, &xpub);
  size_t len = op == 0 ? 65 : op == 2 ? 65 : op == 3 ? 64 : 1;
  uint8_t *sig = malloc(m.count * 65 + 1), *out = malloc(m.count * len + 1);
  for (size_t i = 0; i < m.count; i++) {
    if (op == 1 || op == 2) {
      secp256k1_ecdsa_recoverable_signature rs; int id;
      secp256k1_ecdsa_sign_recoverable(ctx, &rs, msg(&m, i), sk, NULL, NULL);
      secp256k1_ecdsa_recoverable_signature_serialize_compact(ctx, sig + 65 * i, &id, &rs);
      sig[65 * i + 64] = (uint8_t)id;
    } else if (op == 4) {
      secp256k1_schnorrsig_sign32(ctx, sig + 65 * i, msg(&m, i), &kp, aux);
    }
  }
  /* one pass over the messages takes well under a millisecond, so the pass is repeated
     until 50 ms have passed and BENCH_MS is the mean time of one pass */
  double t0 = now_ms(), t1;
  size_t passes = 0;
  do {
    for (size_t i = 0; i < m.count; i++) {
      const uint8_t *h = msg(&m, i), *s = sig + 65 * i;
      uint8_t *o = out + len * i;
      if (op == 0) {
        secp256k1_ecdsa_recoverable_signature rs; int id;
        secp256k1_ecdsa_sign_recoverable(ctx, &rs, h, sk, NULL, NULL);
        secp256k1_ecdsa_recoverable_signature_serialize_compact(ctx, o, &id, &rs);
        o[64] = (uint8_t)id;
      } else if (op == 1) {
        secp256k1_pubkey p; secp256k1_ecdsa_signature es;
        o[0] = secp256k1_ec_pubkey_parse(ctx, &p, pk33, 33) && secp256k1_ecdsa_signature_parse_compact(ctx, &es, s)
               && (secp256k1_ecdsa_signature_normalize(ctx, &es, &es), secp256k1_ecdsa_verify(ctx, &es, h, &p));
      } else if (op == 2) {
        secp256k1_ecdsa_recoverable_signature rs; secp256k1_pubkey p; size_t ol = 65;
        if (secp256k1_ecdsa_recoverable_signature_parse_compact(ctx, &rs, s, s[64]) && secp256k1_ecdsa_recover(ctx, &p, &rs, h))
          secp256k1_ec_pubkey_serialize(ctx, o, &ol, &p, SECP256K1_EC_UNCOMPRESSED);
        else memset(o, 0, 65);
      } else if (op == 3) {
        secp256k1_schnorrsig_sign32(ctx, o, h, &kp, aux);
      } else {
        secp256k1_xonly_pubkey xp;
        o[0] = secp256k1_xonly_pubkey_parse(ctx, &xp, xpk32) && secp256k1_schnorrsig_verify(ctx, s, h, 32, &xp);
      }
    }
    passes++;
  } while ((t1 = now_ms()) - t0 < 50);
  report((t1 - t0) / passes, fold_outputs(out, m.count, len));
  secp256k1_context_destroy(ctx);
  return 0;
}
