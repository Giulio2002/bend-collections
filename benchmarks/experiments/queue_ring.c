/* SUPPLEMENTAL optimized C reference for the ring-buffer src/queue.bend
 * (the back-in/front-out specialization of src/deque.bend: enqueue =
 * push_back, dequeue = pop_front, peek = peek_front). The ring code is the
 * one in benchmarks/experiments/deque_ring.c; only the op selectors differ.
 *
 * NOT an acceptance reference: benchmarks/native/queue.c (pinned, the
 * drifting-window algorithm) stays the canonical comparison until the
 * operator reviews docs/BENCHMARK_CHANGE_PROPOSAL.md. This file is the same
 * driver contract (argv, regions, value stream, checksums) with the SAME ring
 * algorithm as src/deque.bend:
 *
 *   elements front first at slots (lo + j) mod cap, cap = 2^depth, lo < cap;
 *   a deque that never held an element owns no block (the first push
 *   allocates one slot); a push onto a FULL ring (len == cap) copies the
 *   ring, in order, into slots 0 .. len - 1 of a block of 2 cap slots and
 *   sets lo = 0; pops only move lo / shrink len, nothing is cleared.
 *
 * Slots come from the bump arena (reset once per round) like the pinned
 * reference; the modular index is computed with the same compare-and-
 * subtract the Bend code uses (lo + j < 2 cap always holds), which clang
 * compiles to a branchless select.
 */
#include "../native/common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t cap; /* 0 = no block yet */
  uint32_t lo, len;
  uint32_t *slots;
} St;

static inline uint32_t wrap(uint32_t x, uint32_t cap) { return x < cap ? x : x - cap; }

static void dq_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->cap = 0;
  s->lo = 0;
  s->len = 0;
  s->slots = NULL;
}

/* grow a full ring: copy it in order into a block twice as large */
static void grow(St *s) {
  uint32_t cap = s->cap;
  uint32_t *n = (uint32_t *)arena_alloc(2u * (size_t)cap * sizeof(uint32_t));
  uint32_t first = cap - s->lo; /* ring positions before the wrap */
  memcpy(n, s->slots + s->lo, (size_t)first * sizeof(uint32_t));
  memcpy(n + first, s->slots, (size_t)s->lo * sizeof(uint32_t));
  s->slots = n;
  s->cap = 2u * cap;
  s->lo = 0;
}

static inline void first_push(St *s, uint32_t v) {
  s->slots = (uint32_t *)arena_alloc(sizeof(uint32_t));
  s->slots[0] = v;
  s->cap = 1;
  s->lo = 0;
  s->len = 1;
}

static inline void dq_pf(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (s->cap == 0) {
    first_push(s, r);
  } else {
    if (s->len == s->cap) grow(s);
    s->lo = s->lo == 0 ? s->cap - 1 : s->lo - 1;
    s->slots[s->lo] = r;
    s->len++;
  }
  s->chk = mix(s->chk, 1);
}

static inline void dq_pb(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (s->cap == 0) {
    first_push(s, r);
  } else {
    if (s->len == s->cap) grow(s);
    s->slots[wrap(s->lo + s->len, s->cap)] = r;
    s->len++;
  }
  s->chk = mix(s->chk, 1);
}

static inline void dq_popf(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code = 9;
  if (s->len) {
    code = s->slots[s->lo];
    s->lo = wrap(s->lo + 1, s->cap);
    s->len--;
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_popb(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code = 9;
  if (s->len) {
    s->len--;
    code = s->slots[wrap(s->lo + s->len, s->cap)];
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_peekf(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len ? s->slots[s->lo] : 9);
}

static inline void dq_peekb(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len ? s->slots[wrap(s->lo + s->len - 1, s->cap)] : 9);
}

static inline void dq_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len);
}

/* to_list: a real list of cells, built back to front, whose length is folded
 * (the Bend driver conses the elements and folds the list's length). */
typedef struct Cell {
  uint32_t v;
  struct Cell *next;
} Cell;

static inline void dq_to_list(St *s) {
  s->rng = lcg(s->rng);
  size_t mark = arena_off;
  Cell *acc = NULL;
  for (uint32_t j = s->len; j-- > 0;) {
    Cell *c = (Cell *)arena_alloc(sizeof(Cell));
    c->v = s->slots[wrap(s->lo + j, s->cap)];
    c->next = acc;
    acc = c;
  }
  uint32_t n = 0;
  for (Cell *p = acc; p; p = p->next) n++;
  s->chk = mix(s->chk, n);
  arena_off = mark;
}

/* new allocates nothing, as DQ.new does (DE{}) */
static inline void dq_new(St *s) {
  s->rng = lcg(s->rng);
  St fresh;
  dq_init(&fresh, 0);
  St *fp = &fresh;
  keep(fp);
  s->chk = mix(s->chk, fp->len);
}

static inline void dq_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static void dq_settle(St *s) {
  for (uint32_t j = 0; j < s->len; j++) s->chk = mix(s->chk, s->slots[wrap(s->lo + j, s->cap)]);
}

static uint32_t round_qu(uint32_t op, uint32_t size, uint32_t count,
                         uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  dq_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) dq_pb(&s);
  dq_settle(&s);
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pb(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_popf(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_peekf(sp); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_len(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_new(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_to_list(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pb(sp); dq_popf(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_null(sp); } break;
  }
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); dq_null(sp); }
  return mix(mix(s.chk, s.rng), s.len);
}

BENCH_MAIN(round_qu, 2048ull * 1024ull * 1024ull)
