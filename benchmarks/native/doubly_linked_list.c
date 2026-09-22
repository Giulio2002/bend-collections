/* Generational indexed DLL: reusable slots, saturated generations retire.
 * Operator-authorized repair; original reference archived. */
#include "common.h"

#define NULL_OP 99u
#include "dlist_arena.h"

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
