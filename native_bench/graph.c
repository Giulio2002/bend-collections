/* Optimized C reference for src/graph.bend (undirected).
 *
 * Same algorithm and representation: a finite simple graph as an ordered map
 * from each vertex to its ordered set of neighbours, both being the 2-3 tree
 * of native_bench/twothree.h (the U32 instance of the same map the Bend source
 * uses). Adding an existing vertex fails with VertexExists; an endpoint that
 * is not a vertex fails with VertexNotFound; a self loop fails with SelfLoop;
 * adding an existing edge is idempotent; removing an absent edge fails with
 * EdgeNotFound; removing a vertex deletes it and strips it from every other
 * neighbour set. Undirected edges are stored at both endpoints and listed once,
 * from the smaller end. Every failure leaves the graph unchanged.
 */
#include "twothree.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  TT *adj; /* vertex -> (TT* neighbour set, as a uint64 payload) */
} St;

static inline TT *set_of(const TT *adj, uint32_t v, int *present) {
  uint64_t p;
  if (tt_find(adj, v, &p)) {
    *present = 1;
    return (TT *)(uintptr_t)p;
  }
  *present = 0;
  return NULL;
}

static inline void put_set(St *s, uint32_t v, TT *set) {
  s->adj = tt_insert(s->adj, v, (uint64_t)(uintptr_t)set);
}

static void gr_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->adj = NULL;
}

/* remove w from every neighbour set */
static void strip(TT *t, uint32_t w) {
  if (!t) return;
  t->v1 = (uint64_t)(uintptr_t)tt_remove((TT *)(uintptr_t)t->v1, w);
  if (t->kind == 3) t->v2 = (uint64_t)(uintptr_t)tt_remove((TT *)(uintptr_t)t->v2, w);
  strip(t->a, w);
  strip(t->b, w);
  if (t->kind == 3) strip(t->c, w);
}

static inline void gr_av(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t v = r % (size + 1u);
  int have;
  set_of(s->adj, v, &have);
  uint32_t code;
  if (have) {
    code = 2; /* VertexExists */
  } else {
    put_set(s, v, NULL);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void gr_rv(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t v = r % (size + 1u);
  int have;
  set_of(s->adj, v, &have);
  uint32_t code;
  if (!have) {
    code = 3; /* VertexNotFound */
  } else {
    s->adj = tt_remove(s->adj, v);
    strip(s->adj, v);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void gr_ae(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t u = r % (size + 1u);
  uint32_t v = (r >> 16) % (size + 1u);
  int hu, hv;
  TT *su = set_of(s->adj, u, &hu);
  TT *sv = set_of(s->adj, v, &hv);
  uint32_t code;
  if (!hu || !hv) {
    code = 3;
  } else if (u == v) {
    code = 4; /* SelfLoop */
  } else {
    put_set(s, u, tt_insert(su, v, 0));
    su = set_of(s->adj, u, &hu);
    sv = set_of(s->adj, v, &hv);
    put_set(s, v, tt_insert(sv, u, 0));
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void gr_re(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t u = r % (size + 1u);
  uint32_t v = (r >> 16) % (size + 1u);
  int hu, hv;
  TT *su = set_of(s->adj, u, &hu);
  TT *sv = set_of(s->adj, v, &hv);
  uint32_t code;
  uint64_t dummy;
  if (!hu || !hv) {
    code = 3;
  } else if (!tt_find(su, v, &dummy)) {
    code = 5; /* EdgeNotFound */
  } else {
    put_set(s, u, tt_remove(su, v));
    su = set_of(s->adj, u, &hu);
    sv = set_of(s->adj, v, &hv);
    put_set(s, v, tt_remove(sv, u));
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void gr_hv(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t v = r % (size + 1u);
  int have;
  set_of(s->adj, v, &have);
  s->chk = mix(s->chk, have ? 1u : 0u);
}

static inline void gr_he(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t u = r % (size + 1u);
  uint32_t v = (r >> 16) % (size + 1u);
  int hu, hv;
  TT *su = set_of(s->adj, u, &hu);
  set_of(s->adj, v, &hv);
  uint64_t dummy;
  uint32_t code = (!hu || !hv) ? 3u : (tt_find(su, v, &dummy) ? 1u : 0u);
  s->chk = mix(s->chk, code);
}

/* fold the keys of a set in order */
static uint32_t fold_keys(const TT *t, uint32_t c) {
  if (!t) return c;
  c = fold_keys(t->a, c);
  c = mix(c, t->k1);
  c = fold_keys(t->b, c);
  if (t->kind == 3) {
    c = mix(c, t->k2);
    c = fold_keys(t->c, c);
  }
  return c;
}

static inline void gr_nb(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t v = r % (size + 1u);
  int have;
  TT *set = set_of(s->adj, v, &have);
  s->chk = have ? fold_keys(set, s->chk) : mix(s->chk, 3u);
}

static inline void gr_vs(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_keys(s->adj, s->chk);
}

/* undirected edges, listed once from the smaller end, in vertex order */
static uint32_t fold_out(uint32_t u, const TT *set, uint32_t c) {
  if (!set) return c;
  c = fold_out(u, set->a, c);
  if (u < set->k1) c = mix(mix(c, u), set->k1);
  c = fold_out(u, set->b, c);
  if (set->kind == 3) {
    if (u < set->k2) c = mix(mix(c, u), set->k2);
    c = fold_out(u, set->c, c);
  }
  return c;
}

static uint32_t fold_edges(const TT *t, uint32_t c) {
  if (!t) return c;
  c = fold_edges(t->a, c);
  c = fold_out(t->k1, (const TT *)(uintptr_t)t->v1, c);
  c = fold_edges(t->b, c);
  if (t->kind == 3) {
    c = fold_out(t->k2, (const TT *)(uintptr_t)t->v2, c);
    c = fold_edges(t->c, c);
  }
  return c;
}

static inline void gr_es(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_edges(s->adj, s->chk);
}

static inline void gr_new(St *s) {
  s->rng = lcg(s->rng);
  /* vertices(new(False)) is empty, so nothing is folded */
}

static inline void gr_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_gr(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  tt_reset_pool();
  St s;
  gr_init(&s, seed);
  for (uint32_t i = size; i-- > 0;) { /* vertices size-1 .. 0, no stream use */
    put_set(&s, i, NULL);
    s.chk = mix(s.chk, 1);
  }
  for (uint32_t i = 0; i < size; i++) gr_ae(&s, size);
  s.chk = fold_edges(s.adj, s.chk); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) gr_av(&s, size); break;
    case 1: for (uint32_t i = 0; i < count; i++) gr_rv(&s, size); break;
    case 2: for (uint32_t i = 0; i < count; i++) gr_ae(&s, size); break;
    case 3: for (uint32_t i = 0; i < count; i++) gr_re(&s, size); break;
    case 4: for (uint32_t i = 0; i < count; i++) gr_hv(&s, size); break;
    case 5: for (uint32_t i = 0; i < count; i++) gr_he(&s, size); break;
    case 6: for (uint32_t i = 0; i < count; i++) gr_nb(&s, size); break;
    case 7: for (uint32_t i = 0; i < count; i++) gr_vs(&s); break;
    case 8: for (uint32_t i = 0; i < count; i++) gr_es(&s); break;
    case 9: for (uint32_t i = 0; i < count; i++) gr_new(&s); break;
    default: for (uint32_t i = 0; i < count; i++) gr_null(&s); break;
  }
  /* size-independent drain: sixteen has_vertex/has_edge probes */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) {
    gr_hv(&s, size);
    gr_he(&s, size);
  }
  return s.chk;
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024 * 1024);
  tt_init_pool(32ull * 1024ull * 1024ull);
  uint32_t acc_a = 0, acc_b = 0;
  uint64_t t0 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_a = mix(acc_a, round_gr(a.op, a.size, a.count, a.seed + p));
  uint64_t t1 = now_ns();
  uint64_t t2 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_b = mix(acc_b, round_gr(NULL_OP, a.size, a.count, a.seed + p));
  uint64_t t3 = now_ns();
  emit(acc_a, acc_b, t1 - t0, t3 - t2);
  return 0;
}
