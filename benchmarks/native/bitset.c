/* Optimized C reference for src/bitset.bend.
 *
 * Same algorithm, representation and numeric domain: a fixed-size bitset of
 * `len` bits packed LSB-first into ceil(len/32) U32 words with the unused tail
 * of the last word kept zero. get/set/clear are bounds checked and reject an
 * index >= len without changing the state; union/intersection/difference/xor
 * combine word by word and reject operands of a different logical size,
 * returning the left operand unchanged; count and to_list scan every bit of
 * every word (32 * words steps), exactly as word_count and word_members do.
 *
 * src/bitset.bend keeps the words in a Base List; the reference keeps them in
 * a flat malloc'd block, which is the faster faithful C encoding of the same
 * packed-word representation.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t len, nwords;
  uint32_t *w;   /* the bitset */
  uint32_t *b;   /* the second operand of the binary operations */
} St;

static uint32_t words_of(uint32_t len) { return (len + 31u) / 32u; }

static void bs_init(St *s, uint32_t seed, uint32_t len) {
  s->rng = seed;
  s->chk = 0;
  s->len = len;
  s->nwords = words_of(len);
  size_t bytes = (size_t)(s->nwords ? s->nwords : 1) * sizeof(uint32_t);
  s->w = (uint32_t *)calloc(1, bytes);
  s->b = (uint32_t *)calloc(1, bytes);
  if (!s->w || !s->b) {
    fprintf(stderr, "bitset allocation failed\n");
    exit(2);
  }
}

static inline void bs_assign(St *s, uint32_t size, int value) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 7;
  if (i < s->len) {
    if (value)
      s->w[i >> 5] |= 1u << (i & 31u);
    else
      s->w[i >> 5] &= ~(1u << (i & 31u));
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void bs_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 9;
  if (i < s->len) code = (s->w[i >> 5] >> (i & 31u)) & 1u;
  s->chk = mix(s->chk, code);
}

/* the same 32 shifts per word that word_count performs */
static uint32_t bs_count_bits(const St *s) {
  uint32_t total = 0;
  for (uint32_t k = 0; k < s->nwords; k++) {
    uint32_t w = s->w[k];
    for (int j = 0; j < 32; j++) {
      total += w & 1u;
      w >>= 1;
    }
  }
  return total;
}

static inline void bs_count(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, bs_count_bits(s));
}

static inline void bs_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len);
}

static inline void bs_to_list(St *s) {
  s->rng = lcg(s->rng);
  uint32_t c = s->chk;
  for (uint32_t k = 0; k < s->nwords; k++) {
    uint32_t w = s->w[k];
    for (uint32_t j = 0; j < 32u; j++) {
      if (w & 1u) c = mix(c, k * 32u + j);
      w >>= 1;
    }
  }
  s->chk = c;
}

static inline void bs_combine(St *s, int kind) {
  s->rng = lcg(s->rng);
  for (uint32_t k = 0; k < s->nwords; k++) {
    uint32_t a = s->w[k], b = s->b[k];
    s->w[k] = kind == 0 ? (a | b) : kind == 1 ? (a & b)
            : kind == 2 ? (a & ~b) : (a ^ b);
  }
  s->chk = mix(s->chk, 1);
}

/* The Bend driver really builds a one-element bitset, reads it and
 * disposes it; folding a constant here would compare a Bend allocation
 * against no C allocation at all. */
static inline void bs_new(St *s) {
  s->rng = lcg(s->rng);
  uint32_t *w = (uint32_t *)calloc(1, sizeof(uint32_t));
  if (!w) {
    fprintf(stderr, "bitset allocation failed\n");
    exit(2);
  }
  uint32_t len = 0;
  keep(w);
  free(w);
  s->chk = mix(s->chk, len);
}

static inline void bs_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_bs(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  St s;
  bs_init(&s, seed, size);
  for (uint32_t i = 0; i < size; i++) bs_assign(&s, size, 1);
  /* settle: observe the population count and take the operand copy */
  s.chk = mix(s.chk, bs_count_bits(&s));
  memcpy(s.b, s.w, (size_t)(s.nwords ? s.nwords : 1) * sizeof(uint32_t));
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_assign(sp, size, 1); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_assign(sp, size, 0); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_get(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_count(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_len(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_to_list(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_combine(sp, 0); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_combine(sp, 1); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_combine(sp, 2); } break;
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_combine(sp, 3); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_new(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); bs_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); bs_null(sp); }
  uint32_t c = mix(mix(s.chk, s.rng), bs_count_bits(&s));
  free(s.w);
  free(s.b);
  return c;
}

BENCH_MAIN(round_bs, 4ull * 1024ull * 1024ull)
