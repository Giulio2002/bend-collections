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

/* add v to every value of the depth-p subtree rooted at idx */
static inline void tagall(St *s, uint32_t idx, uint32_t p, uint32_t v) {
  if (p == 0) {
    s->sum[idx] += v;
  } else {
    s->sum[idx] += shl(v, p);
    s->lazy[idx] += v;
  }
}

static uint32_t sg_get_at(const St *s, uint32_t i) {
  uint32_t idx = 1, a = 0;
  for (uint32_t p = s->d; p > 0; p--) {
    a += s->lazy[idx];
    uint32_t h = 1u << (p - 1);
    if (i < h) {
      idx = 2 * idx;
    } else {
      i -= h;
      idx = 2 * idx + 1;
    }
  }
  return s->sum[idx] + a;
}

static void sg_set_at(St *s, uint32_t i, uint32_t v) {
  uint32_t path[32];
  uint32_t idx = 1, a = 0, k = 0;
  for (uint32_t p = s->d; p > 0; p--) {
    path[k++] = idx;
    a += s->lazy[idx];
    uint32_t h = 1u << (p - 1);
    if (i < h) {
      idx = 2 * idx;
    } else {
      i -= h;
      idx = 2 * idx + 1;
    }
  }
  s->sum[idx] = v - a;
  for (uint32_t j = k; j-- > 0;) {
    uint32_t q = path[j];               /* node of depth d - j */
    uint32_t w = s->d - j;              /* its width exponent */
    s->sum[q] = s->sum[2 * q] + s->sum[2 * q + 1] + shl(s->lazy[q], w);
  }
}

static uint32_t sg_prefix(const St *s, uint32_t e) {
  uint32_t idx = 1, a = 0, acc = 0, i = e;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t z = s->lazy[idx];
    uint32_t h = 1u << (p - 1);
    if (i < h) {
      a += z;
      idx = 2 * idx;
    } else {
      acc += s->sum[2 * idx] + shl(a + z, p - 1);
      a += z;
      i -= h;
      idx = 2 * idx + 1;
    }
  }
  if (i != 0) acc += s->sum[idx] + a;
  return acc;
}

/* add v to the first i values of the depth-p subtree rooted at idx */
static void sg_padd_go(St *s, uint32_t idx, uint32_t p, uint32_t i, uint32_t v) {
  if (p == 0) {
    if (i != 0) s->sum[idx] += v;
    return;
  }
  uint32_t h = 1u << (p - 1);
  if (i < h) {
    sg_padd_go(s, 2 * idx, p - 1, i, v);
  } else {
    tagall(s, 2 * idx, p - 1, v);
    sg_padd_go(s, 2 * idx + 1, p - 1, i - h, v);
  }
  s->sum[idx] = s->sum[2 * idx] + s->sum[2 * idx + 1] + shl(s->lazy[idx], p);
}

static inline void sg_range_add(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t l = r % (size + 1u);
  uint32_t rr = (r >> 16) % (size + 1u);
  uint32_t code = 7;
  if (l <= rr && rr <= s->n) {
    sg_padd_go(s, 1, s->d, rr, r);
    sg_padd_go(s, 1, s->d, l, 0u - r);
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

static inline void sg_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 1);
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

static uint32_t round_sg(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  St s;
  sg_init(&s, seed, size);
  for (uint32_t i = 0; i < size; i++) sg_set(&s, size);
  s.chk = mix(s.chk, sg_total(&s)); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) sg_range_add(&s, size); break;
    case 1: for (uint32_t i = 0; i < count; i++) sg_get(&s, size); break;
    case 2: for (uint32_t i = 0; i < count; i++) sg_query(&s, size); break;
    case 3: for (uint32_t i = 0; i < count; i++) sg_len(&s); break;
    case 4: for (uint32_t i = 0; i < count; i++) sg_new(&s); break;
    case 5: for (uint32_t i = 0; i < count; i++) sg_from(&s); break;
    case 6: for (uint32_t i = 0; i < count; i++) sg_set(&s, size); break;
    default: for (uint32_t i = 0; i < count; i++) sg_null(&s); break;
  }
  uint32_t c = mix(mix(mix(s.chk, s.rng), s.n), sg_total(&s));
  free(s.sum);
  free(s.lazy);
  return c;
}

BENCH_MAIN(round_sg, 4ull * 1024ull * 1024ull)
