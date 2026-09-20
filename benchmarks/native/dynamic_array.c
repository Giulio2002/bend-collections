/* Optimized C reference for src/dynamic_array.bend.
 *
 * Same algorithm, semantics and numeric domain as the proved Bend source: a
 * growable, bounds-checked sequence of 2^depth optional U32 slots, with
 *
 *   get/set     bounds-checked indexed access,
 *   push        writes slot `length` and, when full, doubles the room, keeping
 *               the old slots and emptying the new half,
 *   pop         clears slot `length - 1`,
 *   clear       empties every slot, keeping the capacity,
 *   reserve     doubles until the request fits, or fails past 2^24,
 *   to_list     walks the whole capacity and conses the occupied values.
 *
 * The depth cap of 24 makes push/reserve past 2^24 elements fail exactly as
 * the Bend API does. src/dynamic_array.bend stores the slots in a Base.Array,
 * which the Bend runtime realises as one contiguous block, so the reference
 * stores them contiguously as well - the fastest faithful C encoding, not a
 * handicapped one. The cons cells to_list produces come from a scratch arena
 * that is rewound after each call.
 */
#include "common.h"

#define NULL_OP 99u
#define LIMIT 24u

typedef struct Cell {
  uint32_t v;
  struct Cell *next;
} Cell;

/* ---- the slot buffer ----
 * Bend's Base.Array of 2^depth slots is realised by the Bend runtime as one
 * contiguous block, so the reference stores the slots contiguously too:
 * indexing is a shift and a load, growth allocates twice the room, copies the
 * old half and empties the new one, exactly as
 * `ANode{arr, empty_slots(depth)}` does.
 */

typedef struct {
  uint32_t v;
  uint8_t present;
} Slot;

static Slot *slots_new(uint32_t depth) {
  size_t n = (size_t)1u << depth;
  Slot *s = (Slot *)calloc(n, sizeof(Slot));
  if (!s) {
    fprintf(stderr, "slot allocation of %zu failed\n", n);
    exit(2);
  }
  return s;
}

typedef struct {
  uint32_t rng, chk;
  uint32_t depth, length;
  Slot *slots;
} St;

static void da_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->depth = 0;
  s->length = 0;
  s->slots = slots_new(0);
}

static inline void da_push(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t code;
  if (s->length < (1u << s->depth)) {
    s->slots[s->length].present = 1;
    s->slots[s->length].v = r;
    s->length++;
    code = 1;
  } else if (s->depth < LIMIT) {
    size_t old = (size_t)1u << s->depth;
    Slot *grown = slots_new(s->depth + 1);
    memcpy(grown, s->slots, old * sizeof(Slot));
    free(s->slots);
    s->slots = grown;
    s->depth++;
    s->slots[s->length].present = 1;
    s->slots[s->length].v = r;
    s->length++;
    code = 1;
  } else {
    code = 7;
  }
  s->chk = mix(s->chk, code);
}

static inline void da_pop(St *s) {
  s->rng = lcg(s->rng);
  uint32_t code;
  if (s->length == 0) {
    code = 9;
  } else {
    s->length--;
    code = s->slots[s->length].present ? s->slots[s->length].v : 9;
    s->slots[s->length].present = 0;
    s->slots[s->length].v = 0;
  }
  s->chk = mix(s->chk, code);
}

static inline void da_get(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 9;
  if (i < s->length) code = s->slots[i].present ? s->slots[i].v : 9;
  s->chk = mix(s->chk, code);
}

static inline void da_set(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t i = r % (size + 1u);
  uint32_t code = 7;
  if (i < s->length) {
    s->slots[i].present = 1;
    s->slots[i].v = r;
    code = 1;
  }
  s->chk = mix(s->chk, code);
}

static inline void da_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->length);
}

static inline void da_cap(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 1u << s->depth);
}

static Cell *collect(const Slot *slots, uint32_t depth, Cell *acc) {
  for (size_t i = (size_t)1u << depth; i-- > 0;) {
    if (slots[i].present) {
      Cell *c = (Cell *)arena_alloc(sizeof(Cell));
      c->v = slots[i].v;
      c->next = acc;
      acc = c;
    }
  }
  return acc;
}

static inline void da_to_list(St *s) {
  s->rng = lcg(s->rng);
  size_t mark = arena_off;
  uint32_t n = 0;
  for (Cell *p = collect(s->slots, s->depth, NULL); p; p = p->next) n++;
  s->chk = mix(s->chk, n);
  arena_off = mark;
}

static inline void da_clear(St *s) {
  s->rng = lcg(s->rng);
  memset(s->slots, 0, ((size_t)1u << s->depth) * sizeof(Slot));
  s->length = 0;
  s->chk = mix(s->chk, 3);
}

static inline void da_reserve(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t want = r % (size + 1u);
  uint32_t code;
  if (want <= (1u << s->depth)) {
    code = 1;
  } else if (want <= (1u << LIMIT)) {
    while ((1u << s->depth) < want) {
      size_t old = (size_t)1u << s->depth;
      Slot *grown = slots_new(s->depth + 1);
      memcpy(grown, s->slots, old * sizeof(Slot));
      free(s->slots);
      s->slots = grown;
      s->depth++;
    }
    code = 1;
  } else {
    code = 7;
  }
  s->chk = mix(s->chk, code);
}

static inline void da_new(St *s) {
  s->rng = lcg(s->rng);
  Slot *fresh = slots_new(0);
  free(fresh);
  s->chk = mix(s->chk, 0);
}

static inline void da_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

/* materialise/observe the built structure before the measured loop, mirroring
 * benchmarks/bend/dynamic_array.bend's settle step */
static void da_settle(St *s) {
  size_t mark = arena_off;
  for (Cell *p = collect(s->slots, s->depth, NULL); p; p = p->next)
    s->chk = mix(s->chk, p->v);
  arena_off = mark;
}

static uint32_t round_da(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  arena_reset();
  St s;
  da_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) da_push(&s);
  da_settle(&s);
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); da_push(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); da_pop(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); da_get(sp, size); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); da_set(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); da_len(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); da_cap(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); da_to_list(sp); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); da_clear(sp); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); da_reserve(sp, size); } break;
    /* restoring pair: the pop is measured together with the push that puts
     * the element back (see benchmarks/bend/dynamic_array.bend) */
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); da_push(sp); da_pop(sp); } break;
    case NULL_OP: for (uint32_t i = 0; i < count; i++) { keep(sp); da_null(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); da_new(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); da_null(sp); }
  /* size-independent drain: the length and a fixed 64 reads from the same
   * value stream, exactly as the Bend driver does */
  uint32_t c = mix(mix(s.chk, s.rng), s.length);
  uint32_t n = s.length;
  for (int i = 0; i < 64; i++) {
    uint32_t r = lcg(s.rng);
    s.rng = r;
    uint32_t idx = r % (n + 1u);
    c = mix(c, (idx < s.length && s.slots[idx].present) ? s.slots[idx].v : 9u);
  }
  free(s.slots);
  return c;
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(512ull * 1024ull * 1024ull);
  BENCH_REGIONS(round_da)
  return 0;
}
