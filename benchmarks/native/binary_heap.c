/* Optimized C reference for src/binary_heap.bend.
 *
 * Same algorithm and representation: a min-heap PACKED IN AN ARRAY, element i
 * having children 2i+1 and 2i+2, with
 *
 *   push              write at index n and sift up while the parent is
 *                     larger (early exit at the first parent that is not),
 *   peek              a[0],
 *   pop               take a[0], move the last element to the root and sift
 *                     it down through the smaller child,
 *   from_list         repeated push into a fresh block,
 *   to_sorted_list    copy the block and drain the copy by repeated root
 *                     removal (the heap is unchanged),
 *   length            the cached size.
 *
 * The block doubles when a push finds it full. The Bend side doubles by
 * sharing the old block as the lower half of a block one level deeper (no
 * copy); this reference allocates the new block from a bump arena and
 * memcpy's, which is what an optimized C growable array does. Everything else
 * is index arithmetic on both sides.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t n, cap;
  uint32_t *a;
} St;

static uint32_t *slots_new(uint32_t cap) {
  return (uint32_t *)arena_alloc((size_t)cap * sizeof(uint32_t));
}

static inline void sift_up(uint32_t *a, uint32_t i, uint32_t x) {
  while (i) {
    uint32_t p = (i - 1u) >> 1;
    if (a[p] <= x) break;
    a[i] = a[p];
    i = p;
  }
  a[i] = x;
}

static inline void sift_down(uint32_t *a, uint32_t n, uint32_t i, uint32_t x) {
  for (;;) {
    uint32_t l = 2u * i + 1u;
    if (l >= n) break;
    uint32_t c = l;
    if (l + 1u < n && a[l + 1u] < a[l]) c = l + 1u;
    if (x <= a[c]) break;
    a[i] = a[c];
    i = c;
  }
  a[i] = x;
}

static void bh_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->n = 0;
  s->cap = 1;
  s->a = slots_new(1);
}

static void bh_grow(St *s) {
  uint32_t *b = slots_new(2u * s->cap);
  memcpy(b, s->a, (size_t)s->cap * sizeof(uint32_t));
  s->a = b;
  s->cap *= 2u;
}

static inline void bh_push(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (s->n == s->cap) bh_grow(s);
  sift_up(s->a, s->n, r);
  s->n++;
  s->chk = mix(s->chk, 1);
}

static inline void bh_pop(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code = 9;
  if (s->n) {
    code = s->a[0];
    s->n--;
    if (s->n) sift_down(s->a, s->n, 0, s->a[s->n]);
  }
  s->chk = mix(s->chk, code);
}

static inline void bh_peek(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->n ? s->a[0] : 9u);
}

static inline void bh_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->n);
}

/* fold the heap in ascending order (to_sorted_list, leaving the heap intact) */
static uint32_t fold_sorted(const St *s, uint32_t c) {
  size_t mark = arena_off;
  uint32_t n = s->n;
  uint32_t *a = slots_new(s->cap);
  memcpy(a, s->a, (size_t)n * sizeof(uint32_t));
  while (n) {
    c = mix(c, a[0]);
    n--;
    if (n) sift_down(a, n, 0, a[n]);
  }
  arena_off = mark;
  return c;
}

static inline void bh_sorted(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_sorted(s, s->chk);
}

static inline void bh_from(St *s) {
  /* eight draws from the same stream, consed newest first, then from_list
   * (which builds a FRESH heap, exactly as the Bend side does) */
  uint32_t vals[8];
  uint32_t r = s->rng;
  for (int i = 0; i < 8; i++) {
    r = lcg(r);
    vals[i] = r;
  }
  s->rng = r;
  s->cap = 1;
  s->a = slots_new(1);
  s->n = 0;
  for (int i = 7; i >= 0; i--) {
    if (s->n == s->cap) bh_grow(s);
    sift_up(s->a, s->n, vals[i]);
    s->n++;
  }
  s->chk = mix(s->chk, 5);
}

static inline void bh_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 0);
}

static inline void bh_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_bh(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  bh_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) bh_push(&s);
  s.chk = fold_sorted(&s, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_push(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_pop(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_peek(sp); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_len(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_from(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_sorted(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_new(sp); } break;
    /* restoring pair: the pop is measured together with the push that puts an
     * element back (see benchmarks/bend/binary_heap.bend) */
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_push(sp); bh_pop(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); bh_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); bh_null(sp); }
  uint32_t c = mix(s.chk, s.rng);
  s.chk = c;
  for (int i = 0; i < 16; i++) bh_peek(&s);
  return s.chk;
}

BENCH_MAIN(round_bh, 1536ull * 1024ull * 1024ull)
