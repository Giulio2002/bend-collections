/* Optimized C reference for src/balanced_search_tree.bend at the U32/U32
 * instance. The red-black tree itself lives in benchmarks/native/redblack.h; this file
 * only drives the same operations with the same value stream and checksum
 * fold as benchmarks/bend/balanced_search_tree.bend.
 */
#include "redblack.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t n;   /* entry count */
  RB *t;
} St;

static void bt_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->n = 0;
  s->t = NULL;
}

static inline void bt_ins(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  int fresh;
  s->t = rb_insert_n(s->t, k, r, &fresh);
  s->n += (uint32_t)fresh;
  s->chk = mix(s->chk, 1);
}

static inline void bt_rm(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  int found;
  s->t = rb_remove_v(s->t, k, &v, &found);
  s->n -= (uint32_t)found;
  s->chk = mix(s->chk, found ? (uint32_t)v : 9u);
}

/* restoring pair: remove a random key of the built range and reinsert the
 * SAME key, so the map keeps its size (see
 * benchmarks/bend/balanced_search_tree.bend) */
static inline void bt_pair_rm(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  int found;
  s->t = rb_remove_v(s->t, k, &v, &found);
  s->n -= (uint32_t)found;
  s->chk = mix(s->chk, found ? (uint32_t)v : 9u);
  int fresh;
  s->t = rb_insert_n(s->t, k, r, &fresh);
  s->n += (uint32_t)fresh;
  s->chk = mix(s->chk, 1);
}

static inline void bt_look(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  s->chk = mix(s->chk, rb_find(s->t, k, &v) ? (uint32_t)v : 9u);
}

static inline void bt_has(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  s->chk = mix(s->chk, rb_find(s->t, k, &v) ? 1u : 0u);
}

static inline void bt_min(St *s) {
  s->rng = lcg(s->rng);
  uint32_t k;
  uint64_t v;
  s->chk = mix(s->chk, rb_min(s->t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

static inline void bt_max(St *s) {
  s->rng = lcg(s->rng);
  uint32_t k;
  uint64_t v;
  s->chk = mix(s->chk, rb_max(s->t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

static inline void bt_lb(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u), ok;
  uint64_t ov;
  s->chk = mix(s->chk, rb_lower(s->t, k, &ok, &ov) ? mix(ok, (uint32_t)ov) : 9u);
}

static inline void bt_range(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t lo = r % (size + 1u);
  uint32_t hi = (r >> 16) % (size + 1u);
  s->chk = rb_range(s->t, lo, hi, s->chk, 1);
}

static inline void bt_to_list(St *s) {
  s->rng = lcg(s->rng);
  s->chk = rb_entries(s->t, s->chk);
}

static inline void bt_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->n);
}

static inline void bt_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 0);
}

static inline void bt_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_bt(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  rb_reset_pool();
  St s;
  bt_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) bt_ins(&s, size);
  s.chk = rb_entries(s.t, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_ins(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_rm(sp, size); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_look(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_has(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_min(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_max(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_lb(sp, size); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_range(sp, size); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_to_list(sp); } break;
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_len(sp); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_new(sp); } break;
    case 11: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_pair_rm(sp, size); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); bt_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); bt_null(sp); }
  uint32_t k;
  uint64_t v;
  uint32_t c = mix(mix(s.chk, s.rng), s.n);
  return mix(c, rb_min(s.t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024 * 1024);
  rb_init_pool(24ull * 1024ull * 1024ull);
  BENCH_REGIONS(round_bt)
  return 0;
}
