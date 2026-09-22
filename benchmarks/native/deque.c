/* User-requested two-list algorithm; selectors, RNG and checksums retained. */
#include "two_list.h"
#define NULL_OP 99u

static uint32_t round_dq(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  dq_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) dq_pb(&s);
  dq_settle(&s);
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pf(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pb(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_popf(sp); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_popb(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_peekf(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_peekb(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_len(sp); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_to_list(sp); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_new(sp); } break;
    /* restoring pairs: the pop is measured together with the push that puts
     * the element back, so the window keeps its size and the batch is not
     * limited to what one build supplies (see benchmarks/bend/deque.bend) */
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pf(sp); dq_popf(sp); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_pb(sp); dq_popb(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); dq_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); dq_null(sp); }
  /* size-independent drain: the length only, as the Bend driver does */
  uint32_t result=mix(mix(s.chk, s.rng), s.len);
  dq_destroy(&s);
  return result;
}

BENCH_MAIN(round_dq, 16)
