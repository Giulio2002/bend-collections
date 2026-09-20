/* Optimized C reference for src/union_find.bend.
 *
 * Same algorithm and semantics: weighted quick-find over 0 .. n-1. Every
 * element's cell stores its class representative directly, so find is a single
 * read; the representative's cell also holds the class size and the list of
 * its members. A union relinks every member of the smaller class (ties keep
 * the first argument's class), concatenates the member lists and decrements
 * the class count. Any index >= n yields OutOfRange without changing the
 * state. This is exactly the "path length at most one" variant documented in
 * src/union_find.bend, not path-halving over a parent forest.
 *
 * src/union_find.bend stores the cells in a persistent vector with O(log n)
 * access; the reference stores them in a flat array, which is the faster
 * faithful C encoding of indexed storage.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct Member {
  uint32_t v;
  struct Member *next;
} Member;

typedef struct {
  uint32_t root;
  uint32_t size;
  Member *members;
  Member *last;
} Cell;

typedef struct {
  uint32_t rng, chk;
  uint32_t n, count;
  Cell *cells;
} St;

static void uf_init(St *s, uint32_t seed, uint32_t n) {
  s->rng = seed;
  s->chk = 0;
  s->n = n;
  s->count = n;
  s->cells = (Cell *)arena_alloc(sizeof(Cell) * (n ? n : 1));
  for (uint32_t i = 0; i < n; i++) {
    Member *m = (Member *)arena_alloc(sizeof(Member));
    m->v = i;
    m->next = NULL;
    s->cells[i].root = i;
    s->cells[i].size = 1;
    s->cells[i].members = m;
    s->cells[i].last = m;
  }
}

static inline void uf_union(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t a = r % (size + 1u);
  uint32_t b = (r >> 16) % (size + 1u);
  uint32_t code;
  if (a >= s->n || b >= s->n) {
    code = 9;
  } else {
    uint32_t ra = s->cells[a].root, rb = s->cells[b].root;
    if (ra == rb) {
      code = 0;
    } else {
      uint32_t big = (s->cells[rb].size <= s->cells[ra].size) ? ra : rb;
      uint32_t small = (big == ra) ? rb : ra;
      for (Member *m = s->cells[small].members; m; m = m->next)
        s->cells[m->v].root = big;
      /* members_small ++ members_big */
      s->cells[small].last->next = s->cells[big].members;
      if (!s->cells[big].last) s->cells[big].last = s->cells[small].last;
      s->cells[big].members = s->cells[small].members;
      s->cells[big].size += s->cells[small].size;
      s->count--;
      code = 1;
    }
  }
  s->chk = mix(s->chk, code);
}

static inline void uf_find(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t x = r % (size + 1u);
  s->chk = mix(s->chk, x < s->n ? s->cells[x].root : 9u);
}

static inline void uf_conn(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t a = r % (size + 1u);
  uint32_t b = (r >> 16) % (size + 1u);
  uint32_t code = 9;
  if (a < s->n && b < s->n) code = (s->cells[a].root == s->cells[b].root) ? 1u : 0u;
  s->chk = mix(s->chk, code);
}

static inline void uf_size(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t x = r % (size + 1u);
  s->chk = mix(s->chk, x < s->n ? s->cells[s->cells[x].root].size : 9u);
}

static inline void uf_count(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->count);
}

/* benchmarks/bend/union_find.bend's `do_new` really builds a one-element
 * union-find, reads its component count and disposes it, so this does the
 * same: it allocates and initialises the one cell and its member list, folds
 * the count, and releases the storage again. Folding the constant 1 here
 * instead would compare a Bend allocation against no C allocation at all. */
static inline void uf_new(St *s) {
  s->rng = lcg(s->rng);
  size_t mark = arena_off;
  Cell *c = (Cell *)arena_alloc(sizeof(Cell));
  Member *m = (Member *)arena_alloc(sizeof(Member));
  m->v = 0;
  m->next = NULL;
  c[0].root = 0;
  c[0].size = 1;
  c[0].members = m;
  c[0].last = m;
  uint32_t count = 1;
  keep(c);
  arena_off = mark;
  s->chk = mix(s->chk, count);
}

static inline void uf_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_uf(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  uf_init(&s, seed, size);
  for (uint32_t i = 0; i < size; i++) uf_union(&s, size);
  /* settle: observe every representative once */
  for (uint32_t i = size; i-- > 0;) s.chk = mix(s.chk, s.cells[i].root);
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_find(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_union(sp, size); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_conn(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_size(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_count(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_new(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); uf_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); uf_null(sp); }
  return mix(mix(s.chk, s.rng), s.count);
}

BENCH_MAIN(round_uf, 1024ull * 1024ull * 1024ull)
