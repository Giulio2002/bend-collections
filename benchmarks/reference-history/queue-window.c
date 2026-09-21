/* Optimized C reference for src/queue.bend.
 *
 * src/queue.bend is the back-in/front-out specialization of src/deque.bend
 * (enqueue = push_back, dequeue = pop_front, peek = peek_front), so this file
 * is the same windowed block restricted to those operations.
 *
 * Same algorithm and representation: the elements live in a window
 * [lo, lo + len) of a block of 2^depth slots, front first, so element j is
 * slot lo + j. push_back writes slot lo + len, push_front writes slot lo - 1,
 * the pops take the slot at their end and move the window, and to_list reads
 * the len slots of the window. When a push has no free slot at its end the
 * block is doubled: a back push keeps every index (the old block is the lower
 * half), a front push moves every index up by the old capacity (the old block
 * becomes the upper half), which is exactly what ANode{a, empty} and
 * ANode{empty, a} do on the Bend side.
 *
 * Slots come from a bump arena; doubling takes a fresh block and moves the
 * window into it. The Bend side pays for initialising the fresh half instead
 * of moving the window; both sides double the block on the same pushes.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct {
  uint32_t rng, chk;
  uint32_t depth;   /* capacity = 1u << depth */
  uint32_t lo, len;
  uint32_t *slots;
} St;

static inline uint32_t cap_of(const St *s) { return 1u << s->depth; }

static void dq_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->depth = 0;
  s->lo = 0;
  s->len = 0;
  s->slots = (uint32_t *)arena_alloc(sizeof(uint32_t));
  s->slots[0] = 0;
}

/* Double the block, keeping the window at the same indices. */
static void grow_back(St *s) {
  uint32_t cap = cap_of(s);
  uint32_t *n = (uint32_t *)arena_alloc(2u * (size_t)cap * sizeof(uint32_t));
  memcpy(n + s->lo, s->slots + s->lo, (size_t)s->len * sizeof(uint32_t));
  s->slots = n;
  s->depth++;
}

/* Double the block, moving the window up by the old capacity. */
static void grow_front(St *s) {
  uint32_t cap = cap_of(s);
  uint32_t *n = (uint32_t *)arena_alloc(2u * (size_t)cap * sizeof(uint32_t));
  memcpy(n + cap + s->lo, s->slots + s->lo, (size_t)s->len * sizeof(uint32_t));
  s->slots = n;
  s->lo += cap;
  s->depth++;
}

static inline void dq_pf(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (s->lo == 0) grow_front(s);
  s->slots[--s->lo] = r;
  s->len++;
  s->chk = mix(s->chk, 1);
}

static inline void dq_pb(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (s->lo + s->len == cap_of(s)) grow_back(s);
  s->slots[s->lo + s->len] = r;
  s->len++;
  s->chk = mix(s->chk, 1);
}

static inline void dq_popf(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code = 9;
  if (s->len) {
    code = s->slots[s->lo];
    s->lo++;
    s->len--;
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_popb(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code = 9;
  if (s->len) {
    s->len--;
    code = s->slots[s->lo + s->len];
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_peekf(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len ? s->slots[s->lo] : 9);
}

static inline void dq_peekb(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len ? s->slots[s->lo + s->len - 1] : 9);
}

static inline void dq_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->len);
}

/* The Bend driver conses the window into a real list and folds its LENGTH:
 * build the same list of cells here, from the back of the window forward. */
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
    c->v = s->slots[s->lo + j];
    c->next = acc;
    acc = c;
  }
  uint32_t n = 0;
  for (Cell *p = acc; p; p = p->next) n++;
  s->chk = mix(s->chk, n);
  arena_off = mark;
}

static inline void dq_new(St *s) {
  s->rng = lcg(s->rng);
  St fresh;
  size_t mark = arena_off;
  dq_init(&fresh, 0);
  arena_off = mark;
  s->chk = mix(s->chk, fresh.len);
}

static inline void dq_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

/* materialise/observe the built structure before the measured loop, mirroring
 * the settle step in the Bend driver */
static void dq_settle(St *s) {
  for (uint32_t j = 0; j < s->len; j++) s->chk = mix(s->chk, s->slots[s->lo + j]);
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
    /* restoring pair: the dequeue is measured together with the enqueue that
     * puts the element back (see benchmarks/bend/queue.bend) */
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pb(sp); dq_popf(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); dq_null(sp); }
  /* size-independent drain: the length only, as the Bend driver does */
  return mix(mix(s.chk, s.rng), s.len);
}

BENCH_MAIN(round_qu, 2048ull * 1024ull * 1024ull)
