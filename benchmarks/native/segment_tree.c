/* Optimized C reference for src/segment_tree.bend.
 *
 * Same algorithm, representation and numeric domain (U32, wrapping mod 2^32):
 * a perfect binary tree of depth d with 2^d >= n leaves. A leaf holds a value;
 * an internal node holds a lazy tag z (a pending addition for everything below
 * it) and the sum of its subtree including its own tag but excluding the tags
 * above it. get and set walk the path accumulating tags (set stores v minus
 * the accumulated tags); a prefix walk adds the sums of fully covered left
 * subtrees, scaled by the tags above them; range_query is a prefix difference
 * and range_add is "add v over the first r, then -v over the first l", where a
 * fully covered subtree only receives a tag. Out-of-range indices and ranges
 * with l > r or r > n are rejected without changing the state.
 *
 * The tree is stored in one heap-ordered block (node 1 is the root, children
 * 2i and 2i+1), the fastest faithful C encoding of the same perfect tree.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t n, d;
  uint32_t *sum;   /* leaf: the value; internal: subtree sum incl. own tag */
  uint32_t *lazy;  /* internal only */
} St;

static uint32_t depth_for(uint32_t n) {
  uint32_t d = 0;
  while ((1u << d) < n) d++;
  return d;
}

static void sg_alloc(St *s, uint32_t n) {
  s->n = n;
  s->d = depth_for(n);
  size_t cells = (size_t)2u << s->d;
  s->sum = (uint32_t *)calloc(cells, sizeof(uint32_t));
  s->lazy = (uint32_t *)calloc(cells, sizeof(uint32_t));
  if (!s->sum || !s->lazy) {
    fprintf(stderr, "segment allocation failed\n");
    exit(2);
  }
}

static void sg_init(St *s, uint32_t seed, uint32_t n) {
  s->rng = seed;
  s->chk = 0;
  sg_alloc(s, n);
}

/* shift that matches U32.shln: a shift of 32 or more yields 0 */
static inline uint32_t shl(uint32_t v, uint32_t k) {
  return k >= 32u ? 0u : (v << k);
}

/* The same flat split-point layout src/segment_tree.bend uses: the value of
 * index t is sum[2^d + t], and the block [o, o + 2^p) keeps its total in
 * sum[o + 2^(p-1)] and its lazy tag in lazy[o + 2^(p-1)]. */

/* the cell that holds the total of the block at remaining depth q, offset o */
static inline uint32_t cell_of(uint32_t q, uint32_t base, uint32_t hq, uint32_t o) {
  return q ? (o + hq) : (base + o);
}

/* add v to every value of the block at remaining depth q, offset o */
static inline void tagall(St *s, uint32_t q, uint32_t base, uint32_t hq, uint32_t o, uint32_t v) {
  if (q == 0) {
    s->sum[base + o] += v;
  } else {
    s->sum[o + hq] += shl(v, q);
    s->lazy[o + hq] += v;
  }
}

static uint32_t sg_get_at(const St *s, uint32_t i) {
  uint32_t o = 0, a = 0, base = 1u << s->d;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t h = 1u << (p - 1);
    a += s->lazy[o + h];
    if (i >= h) {
      i -= h;
      o += h;
    }
  }
  return s->sum[base + o] + a;
}

static void sg_set_at(St *s, uint32_t i, uint32_t v) {
  uint32_t opath[32], hpath[32];
  uint32_t o = 0, a = 0, k = 0, base = 1u << s->d;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t h = 1u << (p - 1);
    opath[k] = o;
    hpath[k] = h;
    k++;
    a += s->lazy[o + h];
    if (i >= h) {
      i -= h;
      o += h;
    }
  }
  s->sum[base + o] = v - a;
  for (uint32_t j = k; j-- > 0;) {
    uint32_t oo = opath[j], h = hpath[j], q = s->d - j - 1, hq = h >> 1;
    s->sum[oo + h] = s->sum[cell_of(q, base, hq, oo)] + s->sum[cell_of(q, base, hq, oo + h)]
                   + shl(s->lazy[oo + h], q + 1);
  }
}

static uint32_t sg_prefix(const St *s, uint32_t e) {
  uint32_t o = 0, a = 0, acc = 0, i = e, base = 1u << s->d;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t h = 1u << (p - 1), q = p - 1, hq = h >> 1;
    uint32_t z = s->lazy[o + h];
    if (i >= h) {
      acc += s->sum[cell_of(q, base, hq, o)] + shl(a + z, q);
      i -= h;
      o += h;
    }
    a += z;
  }
  if (i != 0) acc += s->sum[base + o] + a;
  return acc;
}

/* add v to the first i values of the block at remaining depth p, offset o */
static void sg_padd_go(St *s, uint32_t o, uint32_t p, uint32_t base, uint32_t i, uint32_t v) {
  if (p == 0) {
    if (i != 0) s->sum[base + o] += v;
    return;
  }
  uint32_t h = 1u << (p - 1), q = p - 1, hq = h >> 1;
  if (i < h) {
    sg_padd_go(s, o, q, base, i, v);
  } else {
    tagall(s, q, base, hq, o, v);
    sg_padd_go(s, o + h, q, base, i - h, v);
  }
  s->sum[o + h] = s->sum[cell_of(q, base, hq, o)] + s->sum[cell_of(q, base, hq, o + h)]
                + shl(s->lazy[o + h], p);
}

static inline void sg_range_add(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t l = r % (size + 1u);
  uint32_t rr = (r >> 16) % (size + 1u);
  uint32_t code = 7;
  if (l <= rr && rr <= s->n) {
    sg_padd_go(s, 0, s->d, 1u << s->d, rr, r);
    sg_padd_go(s, 0, s->d, 1u << s->d, l, 0u - r);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void sg_set(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 7;
  if (i < s->n) {
    sg_set_at(s, i, r);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void sg_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  s->chk = mix(s->chk, i < s->n ? sg_get_at(s, i) : 9u);
}

static inline void sg_query(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t l = r % (size + 1u);
  uint32_t rr = (r >> 16) % (size + 1u);
  uint32_t code = 9;
  if (l <= rr && rr <= s->n) code = sg_prefix(s, rr) - sg_prefix(s, l);
  s->chk = mix(s->chk, code);
}

static inline void sg_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->n);
}

/* The Bend driver really builds a one-element segment tree, reads it and
 * disposes it; folding a constant here would compare a Bend allocation
 * against no C allocation at all. */
static inline void sg_new(St *s) {
  s->rng = lcg(s->rng);
  St fresh;
  sg_alloc(&fresh, 1);
  uint32_t len = fresh.n;
  keep(fresh.sum);
  free(fresh.sum);
  free(fresh.lazy);
  s->chk = mix(s->chk, len);
}

static inline void sg_from(St *s) {
  uint32_t vals[8];
  uint32_t r = s->rng;
  for (int i = 0; i < 8; i++) {
    r = lcg(r);
    vals[i] = r;
  }
  s->rng = r;
  free(s->sum);
  free(s->lazy);
  sg_alloc(s, 8);
  for (int i = 7; i >= 0; i--) sg_set_at(s, (uint32_t)(7 - i), vals[i]);
  s->chk = mix(s->chk, 5);
}

static inline void sg_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static inline uint32_t sg_total(const St *s) {
  return sg_prefix(s, s->n) - sg_prefix(s, 0);
}

static uint32_t round_sg(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  St s;
  sg_init(&s, seed, size);
  for (uint32_t i = 0; i < size; i++) sg_set(&s, size);
  s.chk = mix(s.chk, sg_total(&s)); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_range_add(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_get(sp, size); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_query(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_len(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_new(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_from(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_set(sp, size); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); sg_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); sg_null(sp); }
  uint32_t c = mix(mix(mix(s.chk, s.rng), s.n), sg_total(&s));
  free(s.sum);
  free(s.lazy);
  return c;
}

BENCH_MAIN(round_sg, 4ull * 1024ull * 1024ull)
