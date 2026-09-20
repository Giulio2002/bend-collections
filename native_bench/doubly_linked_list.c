/* Optimized C reference for src/doubly_linked_list.bend (U32 values).
 *
 * Same algorithm and representation: the elements are nodes {value, prev id,
 * next id} stored in an ordered map keyed by element id - the same 2-3 tree as
 * the Bend source uses (native_bench/twothree.h) - together with the head and
 * tail ids, the element count, the next fresh id and the list tag. Ids are
 * never reused, so a handle to a removed element is rejected as stale, and a
 * handle whose tag differs from the list's is rejected as foreign. Every
 * failure leaves the list unchanged. A handle operation therefore costs a
 * constant number of O(log n) map lookups and updates, exactly as documented
 * for the Bend API; to_list walks the next links.
 *
 * Node records come from a bump arena reset once per round; the map nodes come
 * from the 2-3 tree pool.
 */
#include "twothree.h"

#define NULL_OP 99u
#define NO_ID 0xFFFFFFFFu

typedef struct {
  uint32_t val;
  uint32_t prev, next; /* NO_ID = none */
} Node;

typedef struct {
  uint32_t rng, chk;
  uint32_t tag, fresh, count;
  uint32_t head, tail;
  TT *nodes;
} St;

static inline Node *node_new(uint32_t v, uint32_t p, uint32_t n) {
  Node *x = (Node *)arena_alloc(sizeof(Node));
  x->val = v;
  x->prev = p;
  x->next = n;
  return x;
}

static inline Node *find_node(const TT *nodes, uint32_t i) {
  uint64_t p;
  if (i == NO_ID) return NULL;
  if (!tt_find(nodes, i, &p)) return NULL;
  return (Node *)(uintptr_t)p;
}

static void dl_init(St *s, uint32_t seed, uint32_t tag) {
  s->rng = seed;
  s->chk = 0;
  s->tag = tag;
  s->fresh = 0;
  s->count = 0;
  s->head = NO_ID;
  s->tail = NO_ID;
  s->nodes = NULL;
}

/* insert a fresh node holding x between a and b */
static uint32_t insert_between(St *s, uint32_t a, uint32_t b, uint32_t x) {
  uint32_t id = s->fresh++;
  Node *nd = node_new(x, a, b);
  s->nodes = tt_insert(s->nodes, id, (uint64_t)(uintptr_t)nd);
  Node *na = find_node(s->nodes, a);
  if (na) na->next = id;
  Node *nb = find_node(s->nodes, b);
  if (nb) nb->prev = id;
  if (a == NO_ID) s->head = id;
  if (b == NO_ID) s->tail = id;
  s->count++;
  return id;
}

static inline uint32_t handle_code(uint32_t tag, uint32_t id) {
  return mix(tag, id);
}

static inline uint32_t draw_id(St *s, uint32_t size, uint32_t r) {
  (void)s;
  return r % (size + 1u);
}

static inline void dl_pf(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t id = insert_between(s, NO_ID, s->head, r);
  s->chk = mix(s->chk, handle_code(s->tag, id));
}

static inline void dl_pb(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t id = insert_between(s, s->tail, NO_ID, r);
  s->chk = mix(s->chk, handle_code(s->tag, id));
}

static inline void dl_ins(St *s, uint32_t size, int after) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = draw_id(s, size, r);
  Node *nd = find_node(s->nodes, i);
  uint32_t code;
  if (!nd) {
    code = 3; /* StaleHandle */
  } else {
    uint32_t id = after ? insert_between(s, i, nd->next, r)
                        : insert_between(s, nd->prev, i, r);
    code = handle_code(s->tag, id);
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_rm(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = draw_id(s, size, r);
  Node *nd = find_node(s->nodes, i);
  uint32_t code;
  if (!nd) {
    code = 3;
  } else {
    uint32_t a = nd->prev, b = nd->next;
    code = nd->val;
    s->nodes = tt_remove(s->nodes, i);
    Node *na = find_node(s->nodes, a);
    if (na) na->next = b;
    Node *nb = find_node(s->nodes, b);
    if (nb) nb->prev = a;
    if (a == NO_ID) s->head = b;
    if (b == NO_ID) s->tail = a;
    s->count--;
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_node(s->nodes, draw_id(s, size, r));
  s->chk = mix(s->chk, nd ? nd->val : 3u);
}

static inline void dl_set(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_node(s->nodes, draw_id(s, size, r));
  if (nd) nd->val = r;
  s->chk = mix(s->chk, nd ? 1u : 3u);
}

static inline void dl_nbr(St *s, uint32_t size, int forward) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  Node *nd = find_node(s->nodes, draw_id(s, size, r));
  uint32_t code;
  if (!nd) {
    code = 3;
  } else {
    uint32_t j = forward ? nd->next : nd->prev;
    code = (j == NO_ID) ? 7u : handle_code(s->tag, j);
  }
  s->chk = mix(s->chk, code);
}

static inline void dl_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->count);
}

static uint32_t fold_list(const St *s, uint32_t c) {
  uint32_t i = s->head;
  for (uint32_t k = 0; k < s->count && i != NO_ID; k++) {
    Node *nd = find_node(s->nodes, i);
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

static uint32_t round_dl(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  tt_reset_pool();
  arena_reset();
  St s;
  dl_init(&s, seed, 1);
  for (uint32_t i = 0; i < size; i++) dl_pb(&s);
  s.chk = fold_list(&s, s.chk); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) dl_pf(&s); break;
    case 1: for (uint32_t i = 0; i < count; i++) dl_pb(&s); break;
    case 2: for (uint32_t i = 0; i < count; i++) dl_ins(&s, size, 0); break;
    case 3: for (uint32_t i = 0; i < count; i++) dl_ins(&s, size, 1); break;
    case 4: for (uint32_t i = 0; i < count; i++) dl_rm(&s, size); break;
    case 5: for (uint32_t i = 0; i < count; i++) dl_get(&s, size); break;
    case 6: for (uint32_t i = 0; i < count; i++) dl_set(&s, size); break;
    case 7: for (uint32_t i = 0; i < count; i++) dl_nbr(&s, size, 1); break;
    case 8: for (uint32_t i = 0; i < count; i++) dl_nbr(&s, size, 0); break;
    case 9: for (uint32_t i = 0; i < count; i++) dl_len(&s); break;
    case 10: for (uint32_t i = 0; i < count; i++) dl_to_list(&s); break;
    case 11: for (uint32_t i = 0; i < count; i++) dl_new(&s); break;
    default: for (uint32_t i = 0; i < count; i++) dl_null(&s); break;
  }
  /* size-independent drain: sixteen gets and the length */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) dl_get(&s, size);
  return mix(s.chk, s.count);
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024ull * 1024ull * 1024ull);
  tt_init_pool(24ull * 1024ull * 1024ull);
  uint32_t acc_a = 0, acc_b = 0;
  uint64_t t0 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_a = mix(acc_a, round_dl(a.op, a.size, a.count, a.seed + p));
  uint64_t t1 = now_ns();
  uint64_t t2 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_b = mix(acc_b, round_dl(NULL_OP, a.size, a.count, a.seed + p));
  uint64_t t3 = now_ns();
  emit(acc_a, acc_b, t1 - t0, t3 - t2);
  return 0;
}
