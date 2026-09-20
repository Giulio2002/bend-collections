/* Optimized C reference for src/queue.bend.
 *
 * src/queue.bend is the back-in/front-out specialization of src/deque.bend
 * (enqueue = push_back, dequeue = pop_front, peek = peek_front), so this file
 * is the same two-list banker's deque restricted to those operations. A
 * dequeue or peek on an empty front first moves half (floor) of the back
 * across, reversing it, exactly as ready_front does.
 *
 * Cells come from a bump arena; drop shares a suffix and take/reverse copy,
 * matching the Bend list operations.
 */
#include "common.h"

#define NULL_OP 99u

typedef struct Cell {
  uint32_t v;
  struct Cell *next;
} Cell;

typedef struct {
  uint32_t rng, chk;
  uint32_t fl, bl;
  Cell *front, *back;
} St;

static inline Cell *cons(uint32_t v, Cell *t) {
  Cell *c = (Cell *)arena_alloc(sizeof(Cell));
  c->v = v;
  c->next = t;
  return c;
}

static Cell *list_drop(Cell *l, uint32_t k) {
  while (k-- && l) l = l->next;
  return l;
}

/* first k cells, copied in order */
static Cell *list_take(Cell *l, uint32_t k) {
  Cell head;
  Cell *tail = &head;
  head.next = NULL;
  while (k-- && l) {
    tail->next = cons(l->v, NULL);
    tail = tail->next;
    l = l->next;
  }
  return head.next;
}

static Cell *list_reverse(Cell *l) {
  Cell *acc = NULL;
  for (; l; l = l->next) acc = cons(l->v, acc);
  return acc;
}

static void dq_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->fl = s->bl = 0;
  s->front = s->back = NULL;
}

static inline void ready_front(St *s) {
  if (s->front) return;
  uint32_t k = s->bl / 2u;
  Cell *b = s->back;
  s->front = list_reverse(list_drop(b, k));
  s->fl = s->bl - k;
  s->back = list_take(b, k);
  s->bl = k;
}

static inline void ready_back(St *s) {
  if (s->back) return;
  uint32_t k = s->fl / 2u;
  Cell *f = s->front;
  s->back = list_reverse(list_drop(f, k));
  s->bl = s->fl - k;
  s->front = list_take(f, k);
  s->fl = k;
}

static inline void dq_pf(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->front = cons(r, s->front);
  s->fl++;
  s->chk = mix(s->chk, 1);
}

static inline void dq_pb(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->back = cons(r, s->back);
  s->bl++;
  s->chk = mix(s->chk, 1);
}

static inline void dq_popf(St *s) {
  s->rng = lcg(s->rng);
  ready_front(s);
  uint32_t code = 9;
  if (s->front) {
    code = s->front->v;
    s->front = s->front->next;
    s->fl--;
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_popb(St *s) {
  s->rng = lcg(s->rng);
  ready_back(s);
  uint32_t code = 9;
  if (s->back) {
    code = s->back->v;
    s->back = s->back->next;
    s->bl--;
  }
  s->chk = mix(s->chk, code);
}

static inline void dq_peekf(St *s) {
  s->rng = lcg(s->rng);
  ready_front(s);
  s->chk = mix(s->chk, s->front ? s->front->v : 9);
}

static inline void dq_peekb(St *s) {
  s->rng = lcg(s->rng);
  ready_back(s);
  s->chk = mix(s->chk, s->back ? s->back->v : 9);
}

static inline void dq_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->fl + s->bl);
}

static inline void dq_to_list(St *s) {
  s->rng = lcg(s->rng);
  size_t mark = arena_off;
  Cell *tail = list_reverse(s->back);
  Cell *out = tail;
  if (s->front) {
    Cell head;
    Cell *t = &head;
    head.next = NULL;
    for (Cell *p = s->front; p; p = p->next) {
      t->next = cons(p->v, NULL);
      t = t->next;
    }
    t->next = tail;
    out = head.next;
  }
  uint32_t n = 0;
  for (Cell *p = out; p; p = p->next) n++;
  s->chk = mix(s->chk, n);
  arena_off = mark;
}

static inline void dq_new(St *s) {
  s->rng = lcg(s->rng);
  St fresh;
  dq_init(&fresh, 0);
  s->chk = mix(s->chk, fresh.fl + fresh.bl);
}

static inline void dq_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

/* materialise/observe the built structure before the measured loop, mirroring
 * the settle step in the Bend driver */
static void dq_settle(St *s) {
  size_t mark = arena_off;
  for (Cell *p = s->front; p; p = p->next) s->chk = mix(s->chk, p->v);
  for (Cell *p = list_reverse(s->back); p; p = p->next) s->chk = mix(s->chk, p->v);
  arena_off = mark;
}

static uint32_t round_qu(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  arena_reset();
  St s;
  dq_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) dq_pb(&s);
  dq_settle(&s);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) dq_pb(&s); break;
    case 1: for (uint32_t i = 0; i < count; i++) dq_popf(&s); break;
    case 2: for (uint32_t i = 0; i < count; i++) dq_peekf(&s); break;
    case 3: for (uint32_t i = 0; i < count; i++) dq_len(&s); break;
    case 4: for (uint32_t i = 0; i < count; i++) dq_new(&s); break;
    case 5: for (uint32_t i = 0; i < count; i++) dq_to_list(&s); break;
    default: for (uint32_t i = 0; i < count; i++) dq_null(&s); break;
  }
  /* size-independent drain: the length only, as the Bend driver does */
  return mix(mix(s.chk, s.rng), s.fl + s.bl);
}

BENCH_MAIN(round_qu, 2048ull * 1024ull * 1024ull)
