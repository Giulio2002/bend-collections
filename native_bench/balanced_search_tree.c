/* Optimized C reference for src/balanced_search_tree.bend at the U32/U32
 * instance. The 2-3 tree itself lives in native_bench/twothree.h; this file
 * only drives the same operations with the same value stream and checksum
 * fold as benchmarks/bend/balanced_search_tree.bend.
 */
#include "twothree.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t n;   /* entry count */
  TT *t;
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
  uint64_t old;
  if (!tt_find(s->t, k, &old)) s->n++;
  s->t = tt_insert(s->t, k, r);
  s->chk = mix(s->chk, 1);
}

static inline void bt_rm(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  uint32_t code = 9;
  if (tt_find(s->t, k, &v)) {
    s->t = tt_remove(s->t, k);
    s->n--;
    code = (uint32_t)v;
  }
  s->chk = mix(s->chk, code);
}

static inline void bt_look(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  s->chk = mix(s->chk, tt_find(s->t, k, &v) ? (uint32_t)v : 9u);
}

static inline void bt_has(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u);
  uint64_t v;
  s->chk = mix(s->chk, tt_find(s->t, k, &v) ? 1u : 0u);
}

static inline void bt_min(St *s) {
  s->rng = lcg(s->rng);
  uint32_t k;
  uint64_t v;
  s->chk = mix(s->chk, tt_min(s->t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

static inline void bt_max(St *s) {
  s->rng = lcg(s->rng);
  uint32_t k;
  uint64_t v;
  s->chk = mix(s->chk, tt_max(s->t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

static inline void bt_lb(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t k = r % (size + 1u), ok;
  uint64_t ov;
  s->chk = mix(s->chk, tt_lower(s->t, k, &ok, &ov) ? mix(ok, (uint32_t)ov) : 9u);
}

static inline void bt_range(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t lo = r % (size + 1u);
  uint32_t hi = (r >> 16) % (size + 1u);
  s->chk = tt_range(s->t, lo, hi, s->chk, 1);
}

static inline void bt_to_list(St *s) {
  s->rng = lcg(s->rng);
  s->chk = tt_entries(s->t, s->chk);
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

static uint32_t round_bt(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  tt_reset_pool();
  St s;
  bt_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) bt_ins(&s, size);
  s.chk = tt_entries(s.t, s.chk); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) bt_ins(&s, size); break;
    case 1: for (uint32_t i = 0; i < count; i++) bt_rm(&s, size); break;
    case 2: for (uint32_t i = 0; i < count; i++) bt_look(&s, size); break;
    case 3: for (uint32_t i = 0; i < count; i++) bt_has(&s, size); break;
    case 4: for (uint32_t i = 0; i < count; i++) bt_min(&s); break;
    case 5: for (uint32_t i = 0; i < count; i++) bt_max(&s); break;
    case 6: for (uint32_t i = 0; i < count; i++) bt_lb(&s, size); break;
    case 7: for (uint32_t i = 0; i < count; i++) bt_range(&s, size); break;
    case 8: for (uint32_t i = 0; i < count; i++) bt_to_list(&s); break;
    case 9: for (uint32_t i = 0; i < count; i++) bt_len(&s); break;
    case 10: for (uint32_t i = 0; i < count; i++) bt_new(&s); break;
    default: for (uint32_t i = 0; i < count; i++) bt_null(&s); break;
  }
  uint32_t k;
  uint64_t v;
  uint32_t c = mix(mix(s.chk, s.rng), s.n);
  return mix(c, tt_min(s.t, &k, &v) ? mix(k, (uint32_t)v) : 9u);
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024 * 1024);
  tt_init_pool(24ull * 1024ull * 1024ull);
  uint32_t acc_a = 0, acc_b = 0;
  uint64_t t0 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_a = mix(acc_a, round_bt(a.op, a.size, a.count, a.seed + p));
  uint64_t t1 = now_ns();
  uint64_t t2 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_b = mix(acc_b, round_bt(NULL_OP, a.size, a.count, a.seed + p));
  uint64_t t3 = now_ns();
  emit(acc_a, acc_b, t1 - t0, t3 - t2);
  return 0;
}
