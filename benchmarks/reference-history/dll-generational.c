/* Generational indexed DLL: reusable slots, saturated generations retire.
 * Operator-authorized repair; original reference archived. */
#include "common.h"

#define NULL_OP 99u
#define NO_ID 0xFFFFFFFFu

typedef struct {
  uint32_t val;
  uint32_t prev, next; /* NO_ID = none */
  uint32_t live, generation;
} Node;

typedef struct {
  uint32_t rng, chk;
  uint32_t tag, fresh, count, free_head;
  uint32_t head, tail;
  uint32_t cap;
  Node *cells;
} St;

static void dl_init(St *s, uint32_t seed, uint32_t tag) {
  s->rng = seed;
  s->chk = 0;
  s->tag = tag;
  s->fresh = 0;
  s->free_head = NO_ID;
  s->count = 0;
  s->head = NO_ID;
  s->tail = NO_ID;
  s->cap = 1;
  s->cells = calloc(1, sizeof(Node));
  if (!s->cells) abort();
  s->cells[0].live = 0;
}

static void dl_grow(St *s) {
  if (s->cap > UINT32_MAX / 2u) abort();
  Node *n = realloc(s->cells, 2u * (size_t)s->cap * sizeof(Node));
  if (!n) abort();
  memset(n + s->cap, 0, (size_t)s->cap * sizeof(Node));
  s->cells = n;
  s->cap *= 2u;
}

static inline Node *find_node(St *s, uint32_t i) {
  if (i >= s->fresh) return NULL;
  Node *nd = &s->cells[i];
  return nd->live ? nd : NULL;
}

static inline Node *find_handle(St *s, uint32_t tag, uint32_t id, uint32_t generation) {
  if (tag != s->tag) return NULL;
  Node *n = find_node(s, id);
  return n && n->generation == generation ? n : NULL;
}

static uint32_t remove_node(St *s, uint32_t id) {
  Node *nd = &s->cells[id];
  uint32_t a=nd->prev, b=nd->next, value=nd->val;
  nd->live=0; nd->val=0;
  if (a != NO_ID) s->cells[a].next=b; else s->head=b;
  if (b != NO_ID) s->cells[b].prev=a; else s->tail=a;
  s->count--;
  /* Saturation is permanent retirement, never generation wraparound. */
  if (nd->generation != UINT32_MAX) {
    nd->generation++;
    nd->next=s->free_head;
    s->free_head=id;
  }
  return value;
}

/* insert a fresh node holding x between a and b */
static uint32_t insert_between(St *s, uint32_t a, uint32_t b, uint32_t x) {
  uint32_t id;
  if (s->free_head != NO_ID) {
    id = s->free_head;
    s->free_head = s->cells[id].next;
  } else {
    if (s->fresh == s->cap) dl_grow(s);
    id = s->fresh++;
  }
  Node *nd = &s->cells[id];
  nd->val = x;
  nd->prev = a;
  nd->next = b;
  nd->live = 1;
  Node *na = find_node(s, a);
  if (na) na->next = id;
  Node *nb = find_node(s, b);
  if (nb) nb->prev = id;
  if (a == NO_ID) s->head = id;
  if (b == NO_ID) s->tail = id;
  s->count++;
  return id;
}

static inline uint32_t handle_code(uint32_t tag, uint32_t id, uint32_t generation) {
  return mix(tag, id) ^ generation;
}

static inline uint32_t draw_id(uint32_t size, uint32_t r) {
  return r % (size + 1u);
}

static inline void dl_pf(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t id = insert_between(s, NO_ID, s->head, r);
  s->chk = mix(s->chk, handle_code(s->tag, id, s->cells[id].generation));
}

static inline void dl_pb(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t id = insert_between(s, s->tail, NO_ID, r);
  s->chk = mix(s->chk, handle_code(s->tag, id, s->cells[id].generation));
}

static inline void dl_ins(St *s, uint32_t size, int after) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = draw_id(size, r);
  Node *nd = find_handle(s, s->tag, i, 0);
  uint32_t code;
  if (!nd) {
    code = 3; /* StaleHandle */
  } else {
    uint32_t a = nd->prev, b = nd->next;
    uint32_t id = after ? insert_between(s, i, b, r)
                        : insert_between(s, a, i, r);
    code = handle_code(s->tag, id, s->cells[id].generation);
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_rm(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = draw_id(size, r);
  Node *nd = find_handle(s, s->tag, i, 0);
  uint32_t code;
  if (!nd) {
    code = 3;
  } else {
    code = remove_node(s, i);
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_handle(s, s->tag, draw_id(size, r), 0);
  s->chk = mix(s->chk, nd ? nd->val : 3u);
}

static inline void dl_set(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_handle(s, s->tag, draw_id(size, r), 0);
  if (nd) nd->val = r;
  s->chk = mix(s->chk, nd ? 1u : 3u);
}

static inline void dl_nbr(St *s, uint32_t size, int forward) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_handle(s, s->tag, draw_id(size, r), 0);
  uint32_t code;
  if (!nd) {
    code = 3;
  } else {
    uint32_t j = forward ? nd->next : nd->prev;
    code = (j == NO_ID) ? 7u : handle_code(s->tag, j, s->cells[j].generation);
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->count);
}

/* the values from the head, as the list the Bend API returns */
/* Optimized observable traversal: no artificial result allocation. */
static uint32_t fold_list(St *s, uint32_t c) {
  uint32_t i = s->head;
  for (uint32_t k = 0; k < s->count && i != NO_ID; k++) {
    Node *nd = find_node(s, i);
    if (!nd) break;
    c = mix(c, nd->val);
    i = nd->next;
  }
  return c;
}

static inline void dl_to_list(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_list(s, s->chk);
}

static inline void dl_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 0);
}

static inline void dl_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_dl(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  dl_init(&s, seed, 1);
  for (uint32_t i = 0; i < size; i++) dl_pb(&s);
  s.chk = fold_list(&s, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_pf(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_pb(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_ins(sp, size, 0); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_ins(sp, size, 1); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_rm(sp, size); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_get(sp, size); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_set(sp, size); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_nbr(sp, size, 1); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_nbr(sp, size, 0); } break;
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_len(sp); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_to_list(sp); } break;
    case 11: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_new(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); dl_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); dl_null(sp); }
  /* size-independent drain: sixteen gets and the length */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) dl_get(&s, size);
  uint32_t result = mix(s.chk, s.count);
  free(s.cells);
  return result;
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(16);
  BENCH_REGIONS(round_dl)
  return 0;
}
