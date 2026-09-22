/* Optimized C reference for the hash table (benchmarks/bend/hash_table.bend
 * over src/hash_table.bend).
 *
 * Design -- a standard efficient open-addressing table:
 *   - buckets hold the key and the value side by side (one cache line per
 *     probe), key 0 = empty (keys are stored as i + 1);
 *   - linear probing, power-of-two size, load <= 1/2, Fibonacci hashing;
 *   - backward-shift deletion, so there are no tombstones;
 *   - the table grows geometrically from 2 buckets, like the Bend table.
 *
 * Keys are uint32 values i; the Bend key is the one-character String
 * Chr{65536 + i}, a bijective image of the same 32-bit identity.
 *
 * argv = [op, size, count, reps, seed, order] (see common.h). A round builds
 * a table holding keys 0 .. size-1 (value i + 1), settles it by folding its
 * size, then runs the measured operation, where the argument of a keyed
 * operation is i = lcg % (size + 1) (usually a hit, sometimes a miss):
 *
 *   0 set       insert/replace i with the drawn value; folds the size
 *   1 get       folds the value, or 2^32-1 when absent
 *   2 has       folds 1 or 0
 *   3 pop+set   pops i (folds the value or 0), sets i back to i + 1
 *   4 size      folds the size
 *   5 keys      folds the key count and the sum of key codes (order-free)
 *   6 build     builds a new table of keys 0 .. size-1 from empty (growth
 *               included); folds its size
 *   else        value-stream step only
 *
 * The drain: sixteen gets and the size.
 */
#include "common.h"

#define NONE 0xFFFFFFFFu

typedef struct {
  uint32_t key; /* i + 1; 0 = empty */
  uint32_t val;
} Bucket;

typedef struct {
  uint32_t n, bits;
  Bucket *b;
} Ht;

typedef struct {
  uint32_t rng, chk;
  Ht t;
} St;

static inline uint32_t home(uint32_t k, uint32_t bits) {
  return (k * 0x9E3779B1u) >> (32u - bits);
}

static void ht_init(Ht *t) {
  t->n = 0;
  t->bits = 1;
  t->b = (Bucket *)arena_alloc(2 * sizeof(Bucket));
  memset(t->b, 0, 2 * sizeof(Bucket));
}

static inline void put_raw(Bucket *b, uint32_t bits, uint32_t k, uint32_t v) {
  uint32_t mask = (1u << bits) - 1u;
  uint32_t i = home(k, bits);
  while (b[i].key) i = (i + 1u) & mask;
  b[i].key = k;
  b[i].val = v;
}

static void grow(Ht *t) {
  uint32_t nb = 1u << t->bits, bits = t->bits + 1u;
  Bucket *nw = (Bucket *)arena_alloc((size_t)2 * nb * sizeof(Bucket));
  memset(nw, 0, (size_t)2 * nb * sizeof(Bucket));
  for (uint32_t j = 0; j < nb; j++)
    if (t->b[j].key) put_raw(nw, bits, t->b[j].key, t->b[j].val);
  t->b = nw;
  t->bits = bits;
}

/* the bucket holding k, or the empty bucket ending its probe */
static inline uint32_t find(const Ht *t, uint32_t k) {
  uint32_t mask = (1u << t->bits) - 1u;
  uint32_t i = home(k, t->bits);
  while (t->b[i].key && t->b[i].key != k) i = (i + 1u) & mask;
  return i;
}

static inline void ht_set(Ht *t, uint32_t key, uint32_t v) {
  uint32_t k = key + 1u;
  if (2u * (t->n + 1u) > (1u << t->bits)) grow(t);
  uint32_t i = find(t, k);
  if (!t->b[i].key) { t->b[i].key = k; t->n++; }
  t->b[i].val = v;
}

static inline uint32_t ht_get(const Ht *t, uint32_t key, int *found) {
  uint32_t i = find(t, key + 1u);
  *found = t->b[i].key != 0;
  return *found ? t->b[i].val : NONE;
}

/* backward-shift deletion of the entry in bucket i */
static inline void del_at(Ht *t, uint32_t i) {
  uint32_t mask = (1u << t->bits) - 1u;
  uint32_t j = i;
  for (;;) {
    j = (j + 1u) & mask;
    if (!t->b[j].key) break;
    uint32_t h = home(t->b[j].key, t->bits);
    if (((j - h) & mask) >= ((j - i) & mask)) {
      t->b[i] = t->b[j];
      i = j;
    }
  }
  t->b[i].key = 0;
  t->b[i].val = 0;
  t->n--;
}

static inline uint32_t ht_pop(Ht *t, uint32_t key, int *found) {
  uint32_t i = find(t, key + 1u);
  *found = t->b[i].key != 0;
  if (!*found) return 0;
  uint32_t v = t->b[i].val;
  del_at(t, i);
  return v;
}

static inline uint32_t fold_keys(const Ht *t, uint32_t c) {
  uint32_t nb = 1u << t->bits, cnt = 0, sum = 0;
  for (uint32_t j = 0; j < nb; j++)
    if (t->b[j].key) { cnt++; sum += t->b[j].key - 1u + 65536u; }
  return mix(mix(c, cnt), sum);
}

static void build(Ht *t, uint32_t size) {
  ht_init(t);
  for (uint32_t i = 0; i < size; i++) ht_set(t, i, i + 1u);
}

static inline uint32_t draw(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  return r % (size + 1u);
}

static inline void op_set(St *s, uint32_t size) {
  uint32_t i = draw(s, size);
  ht_set(&s->t, i, s->rng);
  s->chk = mix(s->chk, s->t.n);
}

static inline void op_get(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, ht_get(&s->t, i, &f));
}

static inline void op_has(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  ht_get(&s->t, i, &f);
  s->chk = mix(s->chk, (uint32_t)f);
}

static inline void op_pop_set(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, ht_pop(&s->t, i, &f));
  ht_set(&s->t, i, i + 1u);
}

static inline void op_size(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->t.n);
}

static inline void op_keys(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_keys(&s->t, s->chk);
}

static inline void op_build(St *s, uint32_t size) {
  s->rng = lcg(s->rng);
  Ht g;
  Ht *gp = &g;
  build(gp, size);
  keep(gp);
  s->chk = mix(s->chk, gp->n);
}

static inline void op_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_ht(uint32_t op, uint32_t size, uint32_t count,
                         uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  s.rng = seed;
  s.chk = 0;
  build(&s.t, size);
  s.chk = mix(s.chk, s.t.n); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); op_set(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); op_get(sp, size); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); op_has(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); op_pop_set(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); op_size(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); op_keys(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); op_build(sp, size); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); op_null(sp); } break;
  }
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); op_null(sp); }
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) op_get(&s, size);
  return mix(s.chk, s.t.n);
}

BENCH_MAIN(round_ht, 4096ull * 1024ull * 1024ull)
