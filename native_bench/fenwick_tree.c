/* Optimized C reference for src/fenwick_tree.bend.
 *
 * Same algorithm, representation and numeric domain (U32, wrapping mod 2^32):
 * the Fenwick partial sums live in a perfect binary tree of depth d with
 * 2^d >= n leaves, every internal node holding the sum of its left subtree.
 * A point addition adds v to the left-sums where the root-to-leaf path turns
 * left and to the leaf; a prefix sum adds the left-sums where the path turns
 * right, plus the leaf when the remaining count is positive; a range sum is
 * the difference of two prefix sums. add past index n fails with
 * IndexOutOfRange, prefix_sum(e > n) and range_sum unless l <= r <= n fail
 * with InvalidRange, in both cases leaving the state alone.
 *
 * The tree is stored in one heap-ordered block (node 1 is the root, children
 * 2i and 2i+1), the fastest faithful C encoding of the same perfect tree.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t n, d;
  uint32_t *t;   /* 2^(d+1) entries; internal = left sum, leaf = value */
} St;

static uint32_t depth_for(uint32_t n) {
  uint32_t d = 0;
  while ((1u << d) < n) d++;
  return d;
}

static void fw_alloc(St *s, uint32_t n) {
  s->n = n;
  s->d = depth_for(n);
  size_t cells = (size_t)2u << s->d;
  s->t = (uint32_t *)calloc(cells, sizeof(uint32_t));
  if (!s->t) {
    fprintf(stderr, "fenwick allocation failed\n");
    exit(2);
  }
}

static void fw_init(St *s, uint32_t seed, uint32_t n) {
  s->rng = seed;
  s->chk = 0;
  fw_alloc(s, n);
}

static void fw_point_add(St *s, uint32_t i, uint32_t v) {
  uint32_t idx = 1;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t h = 1u << (p - 1);
    if (i < h) {
      s->t[idx] += v;
      idx = 2 * idx;
    } else {
      i -= h;
      idx = 2 * idx + 1;
    }
  }
  s->t[idx] += v;
}

static uint32_t fw_prefix(const St *s, uint32_t e) {
  uint32_t idx = 1, acc = 0, i = e;
  for (uint32_t p = s->d; p > 0; p--) {
    uint32_t h = 1u << (p - 1);
    if (i < h) {
      idx = 2 * idx;
    } else {
      acc += s->t[idx];
      i -= h;
      idx = 2 * idx + 1;
    }
  }
  if (i != 0) acc += s->t[idx];
  return acc;
}

static inline void fw_add(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 7;
  if (i < s->n) {
    fw_point_add(s, i, r);
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void fw_prefix_op(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t e = r % (size + 1u);
  s->chk = mix(s->chk, e <= s->n ? fw_prefix(s, e) : 9u);
}

static inline void fw_range(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t l = r % (size + 1u);
  uint32_t rr = (r >> 16) % (size + 1u);
  uint32_t code = 9;
  if (l <= rr && rr <= s->n) code = fw_prefix(s, rr) - fw_prefix(s, l);
  s->chk = mix(s->chk, code);
}

static inline void fw_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->n);
}

static inline void fw_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 1); /* length(new(1)) */
}

static inline void fw_from(St *s) {
  uint32_t vals[8];
  uint32_t r = s->rng;
  for (int i = 0; i < 8; i++) {
    r = lcg(r);
    vals[i] = r;
  }
  s->rng = r;
  free(s->t);
  fw_alloc(s, 8);
  for (int i = 7; i >= 0; i--) fw_point_add(s, (uint32_t)(7 - i), vals[i]);
  s->chk = mix(s->chk, 5);
}

static inline void fw_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_fw(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  St s;
  fw_init(&s, seed, size);
  for (uint32_t i = 0; i < size; i++) fw_add(&s, size);
  s.chk = mix(s.chk, fw_prefix(&s, s.n)); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) fw_add(&s, size); break;
    case 1: for (uint32_t i = 0; i < count; i++) fw_prefix_op(&s, size); break;
    case 2: for (uint32_t i = 0; i < count; i++) fw_range(&s, size); break;
    case 3: for (uint32_t i = 0; i < count; i++) fw_len(&s); break;
    case 4: for (uint32_t i = 0; i < count; i++) fw_new(&s); break;
    case 5: for (uint32_t i = 0; i < count; i++) fw_from(&s); break;
    default: for (uint32_t i = 0; i < count; i++) fw_null(&s); break;
  }
  uint32_t c = mix(mix(mix(s.chk, s.rng), s.n), fw_prefix(&s, s.n));
  free(s.t);
  return c;
}

BENCH_MAIN(round_fw, 4ull * 1024ull * 1024ull)
