/* Optimized C reference for src/graph.bend (undirected).
 *
 * Same algorithm and representation: a finite simple graph as an ordered map
 * from each vertex to its ordered set of neighbours, both being the red-black tree
 * of benchmarks/native/redblack.h (the U32 instance of the same map the Bend source
 * uses). Adding an existing vertex fails with VertexExists; an endpoint that
 * is not a vertex fails with VertexNotFound; a self loop fails with SelfLoop;
 * adding an existing edge is idempotent; removing an absent edge fails with
 * EdgeNotFound; removing a vertex deletes it and strips it from every other
 * neighbour set. Undirected edges are stored at both endpoints and listed once,
 * from the smaller end. Every failure leaves the graph unchanged.
 */
#include "redblack.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  RB *adj; /* vertex -> (RB* neighbour set, as a uint64 payload) */
} St;

static inline RB *set_of(const RB *adj, uint32_t v, int *present) {
  uint64_t p;
  if (rb_find(adj, v, &p)) {
    *present = 1;
    return (RB *)(uintptr_t)p;
  }
  *present = 0;
  return NULL;
}

static inline void put_set(St *s, uint32_t v, RB *set) {
  s->adj = rb_insert(s->adj, v, (uint64_t)(uintptr_t)set);
}

static void gr_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->adj = NULL;
}

/* remove w from every neighbour set */
static void strip(RB *t, uint32_t w) {
  if (!t) return;
  t->v = (uint64_t)(uintptr_t)rb_remove((RB *)(uintptr_t)t->v, w);
  strip(t->l, w);
  strip(t->r, w);
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
    s->adj = rb_remove(s->adj, v);
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
  RB *su = set_of(s->adj, u, &hu);
  RB *sv = set_of(s->adj, v, &hv);
  uint32_t code;
  if (!hu || !hv) {
    code = 3;
  } else if (u == v) {
    code = 4; /* SelfLoop */
  } else {
    put_set(s, u, rb_insert(su, v, 0));
    su = set_of(s->adj, u, &hu);
    sv = set_of(s->adj, v, &hv);
    put_set(s, v, rb_insert(sv, u, 0));
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
  RB *su = set_of(s->adj, u, &hu);
  RB *sv = set_of(s->adj, v, &hv);
  uint32_t code;
  uint64_t dummy;
  int found;
  if (!hu || !hv) {
    code = 3;
  } else {
    /* one descent: the removal itself reports whether the edge was there,
     * as `Map.remove` does on the Bend side */
    RB *su2 = rb_remove_v(su, v, &dummy, &found);
    if (!found) {
      code = 5; /* EdgeNotFound */
    } else {
      put_set(s, u, su2);
      su = set_of(s->adj, u, &hu);
      sv = set_of(s->adj, v, &hv);
      put_set(s, v, rb_remove(sv, u));
      code = 1;
    }
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
  RB *su = set_of(s->adj, u, &hu);
  set_of(s->adj, v, &hv);
  uint64_t dummy;
  uint32_t code = (!hu || !hv) ? 3u : (rb_find(su, v, &dummy) ? 1u : 0u);
  s->chk = mix(s->chk, code);
}

/* fold the keys of a set in order */
static uint32_t fold_keys(const RB *t, uint32_t c) {
  if (!t) return c;
  c = fold_keys(t->l, c);
  c = mix(c, t->k);
  return fold_keys(t->r, c);
}

static inline void gr_nb(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t v = r % (size + 1u);
  int have;
  RB *set = set_of(s->adj, v, &have);
  s->chk = have ? fold_keys(set, s->chk) : mix(s->chk, 3u);
}

static inline void gr_vs(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_keys(s->adj, s->chk);
}

/* undirected edges, listed once from the smaller end, in vertex order */
static uint32_t fold_out(uint32_t u, const RB *set, uint32_t c) {
  if (!set) return c;
  c = fold_out(u, set->l, c);
  if (u < set->k) c = mix(mix(c, u), set->k);
  return fold_out(u, set->r, c);
}

static uint32_t fold_edges(const RB *t, uint32_t c) {
  if (!t) return c;
  c = fold_edges(t->l, c);
  c = fold_out(t->k, (const RB *)(uintptr_t)t->v, c);
  return fold_edges(t->r, c);
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

static uint32_t round_gr(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  rb_reset_pool();
  St s;
  gr_init(&s, seed);
  for (uint32_t i = size; i-- > 0;) { /* vertices size-1 .. 0, no stream use */
    put_set(&s, i, NULL);
    s.chk = mix(s.chk, 1);
  }
  for (uint32_t i = 0; i < size; i++) gr_ae(&s, size);
  s.chk = fold_edges(s.adj, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_av(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_rv(sp, size); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_ae(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_re(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_hv(sp, size); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_he(sp, size); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_nb(sp, size); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_vs(sp); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_es(sp); } break;
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_new(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); gr_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); gr_null(sp); }
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
  rb_init_pool(32ull * 1024ull * 1024ull);
  BENCH_REGIONS(round_gr)
  return 0;
}
