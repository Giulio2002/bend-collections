/* Optimized C reference for src/containers/bitlist.bend.
 *
 * Same algorithm, representation and numeric domain: a growable list of
 * `len` bits packed LSB-first into a doubling array of U32 words (the
 * dynamic array of the Bend side), with every stored bit at a position
 * >= len kept zero. push appends a word only when every stored bit is in
 * use (a zero bit pushed into stored space only bumps the length); pop
 * clears the bit it removes and never shrinks the words; get/set are bounds
 * checked and reject an index >= len without changing the state; count
 * skips zero words and shifts 32 times through the others (the Bend
 * count_word); to_list reads the first len bits in order.
 */
#include "common.h"

typedef struct {
  uint32_t rng, chk;
  uint32_t len, nwords, cap;
  uint32_t *w;
} St;

static void bl_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->len = 0;
  s->nwords = 0;
  s->cap = 1;
  s->w = (uint32_t *)calloc(1, sizeof(uint32_t));
  if (!s->w) {
    fprintf(stderr, "bitlist allocation failed\n");
    exit(2);
  }
}

static inline void bl_push_bit(St *s, uint32_t v) {
  if (s->len == s->nwords * 32u) {
    if (s->nwords == s->cap) {
      s->cap *= 2u;
      s->w = (uint32_t *)realloc(s->w, (size_t)s->cap * sizeof(uint32_t));
      if (!s->w) {
        fprintf(stderr, "bitlist allocation failed\n");
        exit(2);
      }
    }
    s->w[s->nwords++] = v;
  } else if (v) {
    s->w[s->len >> 5] |= 1u << (s->len & 31u);
  }
  s->len++;
}

static inline void bl_push(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  bl_push_bit(s, r & 1u);
  s->chk = mix(s->chk, 1u);
}

static inline void bl_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 9;
  if (i < s->len) code = (s->w[i >> 5] >> (i & 31u)) & 1u;
  s->chk = mix(s->chk, code);
}

static inline void bl_set(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 7;
  if (i < s->len) {
    s->w[i >> 5] |= 1u << (i & 31u);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void bl_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len);
}

static uint32_t bl_count_bits(const St *s) {
  uint32_t total = 0;
  for (uint32_t k = 0; k < s->nwords; k++) {
    uint32_t w = s->w[k];
    if (w == 0) continue;
    for (int j = 0; j < 32; j++) {
      total += w & 1u;
      w >>= 1;
    }
  }
  return total;
}

static inline void bl_count(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, bl_count_bits(s));
}

static inline void bl_to_list(St *s) {
  s->rng = lcg(s->rng);
  uint32_t c = s->chk;
  for (uint32_t i = 0; i < s->len; i++)
    c = mix(c, (s->w[i >> 5] >> (i & 31u)) & 1u);
  s->chk = c;
}

/* pop, then push the popped bit back: the list keeps its length */
static inline void bl_pair(St *s) {
  s->rng = lcg(s->rng);
  if (s->len == 0) {
    s->chk = mix(s->chk, 9u);
    return;
  }
  uint32_t m = s->len - 1u;
  uint32_t b = (s->w[m >> 5] >> (m & 31u)) & 1u;
  if (b) s->w[m >> 5] &= ~(1u << (m & 31u));
  s->len = m;
  s->chk = mix(s->chk, b);
  bl_push_bit(s, b);
}

/* The Bend driver really builds an empty bitlist (a one-word array) and
 * reads its length; folding a constant here would compare a Bend
 * allocation against no C allocation at all. */
static inline void bl_new(St *s) {
  s->rng = lcg(s->rng);
  uint32_t *w = (uint32_t *)calloc(1, sizeof(uint32_t));
  if (!w) {
    fprintf(stderr, "bitlist allocation failed\n");
    exit(2);
  }
  uint32_t len = 0;
  keep(w);
  free(w);
  s->chk = mix(s->chk, len);
}

static inline void bl_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_bl(uint32_t op, uint32_t size, uint32_t count,
                         uint32_t nulls, uint32_t seed) {
  St s;
  bl_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) bl_push(&s);
  s.chk = mix(s.chk, bl_count_bits(&s));
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_push(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_get(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_set(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_len(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_count(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_to_list(sp); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_pair(sp); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_new(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); bl_null(sp); } break;
  }
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); bl_null(sp); }
  uint32_t c = mix(mix(s.chk, s.rng), bl_count_bits(&s));
  free(s.w);
  return c;
}

BENCH_MAIN(round_bl, 1ull * 1024ull * 1024ull)
