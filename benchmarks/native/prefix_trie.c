/* Optimized C reference for src/prefix_trie.bend (U32 values).
 *
 * Same algorithm and representation: a first-child/next-sibling trie whose
 * sibling lists are kept in strictly increasing character-code order, so a
 * preorder walk enumerates keys in String order. A node holds one character,
 * the value of the key spelled by the path ending at it, its child list and
 * its next sibling; the trie root additionally carries the value of the empty
 * key. Removal prunes a node that is left with neither a value nor children.
 * lookup/remove of an absent key and longest_prefix with no matching key
 * report KeyNotFound and leave the state alone.
 *
 * Nodes are mutated in place and come from a bump arena that is reset once per
 * round; pruned nodes go back on a free list.
 */
#include "common.h"

#define NULL_OP 99u
#define KLEN 10u

typedef struct TN {
  uint32_t c;
  int has;
  uint32_t val;
  struct TN *down, *next;
} TN;

static TN *tn_pool = NULL;
static TN *tn_free = NULL;
static size_t tn_cap = 0, tn_used = 0;

static void tn_init(size_t count) {
  tn_pool = (TN *)malloc(sizeof(TN) * count);
  if (!tn_pool) {
    fprintf(stderr, "trie pool allocation failed\n");
    exit(2);
  }
  tn_cap = count;
  tn_used = 0;
  tn_free = NULL;
}

static inline TN *tn_alloc(void) {
  TN *n = tn_free;
  if (n) {
    tn_free = n->down;
  } else {
    if (tn_used == tn_cap) {
      fprintf(stderr, "trie pool exhausted (%zu)\n", tn_cap);
      exit(2);
    }
    n = &tn_pool[tn_used++];
  }
  n->has = 0;
  n->val = 0;
  n->down = n->next = NULL;
  return n;
}

static inline void tn_release(TN *n) {
  n->down = tn_free;
  tn_free = n;
}

typedef struct {
  uint32_t rng, chk;
  int has_root;
  uint32_t root_val;
  TN *kids;
} St;

/* a path spelling key[i..] ending in v, followed by `next` */
static TN *chain(const uint32_t *key, uint32_t i, uint32_t m, uint32_t v, TN *next) {
  TN *n = tn_alloc();
  n->c = key[i];
  n->next = next;
  if (i + 1 == m) {
    n->has = 1;
    n->val = v;
  } else {
    n->down = chain(key, i + 1, m, v, NULL);
  }
  return n;
}

static TN *tn_ins(TN *t, const uint32_t *key, uint32_t i, uint32_t m, uint32_t v) {
  if (!t) return chain(key, i, m, v, NULL);
  if (key[i] < t->c) return chain(key, i, m, v, t);
  if (key[i] > t->c) {
    t->next = tn_ins(t->next, key, i, m, v);
    return t;
  }
  if (i + 1 == m) {
    t->has = 1;
    t->val = v;
  } else {
    t->down = tn_ins(t->down, key, i + 1, m, v);
  }
  return t;
}

static int tn_find(const TN *t, const uint32_t *key, uint32_t i, uint32_t m, uint32_t *out) {
  while (t) {
    if (key[i] < t->c) return 0;
    if (key[i] > t->c) {
      t = t->next;
      continue;
    }
    if (i + 1 == m) {
      if (!t->has) return 0;
      *out = t->val;
      return 1;
    }
    t = t->down;
    i++;
  }
  return 0;
}

static inline TN *prune(TN *t) {
  if (!t->has && !t->down) {
    TN *nx = t->next;
    tn_release(t);
    return nx;
  }
  return t;
}

/* Remove reporting whether the key was there and what it mapped to, in the
 * SAME descent: `PrefixTrie.remove` on the Bend side returns the old value
 * from its own single walk, so a reference that searched first and removed
 * afterwards would walk the trie twice for the same result. */
static TN *tn_rem(TN *t, const uint32_t *key, uint32_t i, uint32_t m,
                  uint32_t *old, int *found) {
  if (!t) return NULL;
  if (key[i] < t->c) return t;
  if (key[i] > t->c) {
    t->next = tn_rem(t->next, key, i, m, old, found);
    return t;
  }
  if (i + 1 == m) {
    if (t->has) {
      *old = t->val;
      *found = 1;
    }
    t->has = 0;
    return prune(t);
  }
  t->down = tn_rem(t->down, key, i + 1, m, old, found);
  return prune(t);
}

/* ---- folds (in key order) ---- */

static uint32_t buf[64];

static uint32_t fold_entry(uint32_t c, uint32_t depth, uint32_t v) {
  for (uint32_t i = 0; i < depth; i++) c = mix(c, buf[i]);
  return mix(c, v);
}

/* every entry of a sibling list, keys relative to `depth` characters in buf */
static uint32_t fold_ent(const TN *t, uint32_t depth, uint32_t c) {
  for (; t; t = t->next) {
    buf[depth] = t->c;
    if (t->has) c = fold_entry(c, depth + 1, t->val);
    c = fold_ent(t->down, depth + 1, c);
  }
  return c;
}

static uint32_t fold_pe(const TN *t, const uint32_t *key, uint32_t i, uint32_t m,
                        uint32_t depth, uint32_t c) {
  while (t) {
    if (key[i] < t->c) return c;
    if (key[i] > t->c) {
      t = t->next;
      continue;
    }
    buf[depth] = t->c;
    if (i + 1 == m) {
      if (t->has) c = fold_entry(c, depth + 1, t->val);
      return fold_ent(t->down, depth + 1, c);
    }
    t = t->down;
    i++;
    depth++;
  }
  return c;
}

/* deepest stored key along key[i..]; returns its length (0 = none) */
static uint32_t tn_lp(const TN *t, const uint32_t *key, uint32_t i, uint32_t m,
                      uint32_t depth, uint32_t *val) {
  while (t) {
    if (key[i] < t->c) return 0;
    if (key[i] > t->c) {
      t = t->next;
      continue;
    }
    uint32_t best = 0;
    if (i + 1 < m) best = tn_lp(t->down, key, i + 1, m, depth + 1, val);
    if (best) return best;
    if (t->has) {
      *val = t->val;
      return depth + 1;
    }
    return 0;
  }
  return 0;
}

/* ---- the driver ---- */

/* character i always reads the same two bits, so a 2-character key really is
 * a prefix of a 6-character one */
static void key_of(uint32_t m, uint32_t r, uint32_t *key) {
  for (uint32_t i = 0; i < m; i++)
    key[i] = 97u + ((r >> ((16u + 2u * i) % 30u)) & 3u);
}

static void pt_init(St *s, uint32_t seed) {
  s->rng = seed;
  s->chk = 0;
  s->has_root = 0;
  s->root_val = 0;
  s->kids = NULL;
}

static inline void pt_ins(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN];
  key_of(KLEN, r, key);
  s->kids = tn_ins(s->kids, key, 0, KLEN, r);
  s->chk = mix(s->chk, 1);
}

static inline void pt_rm(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN], v = 0;
  key_of(KLEN, r, key);
  int found = 0;
  s->kids = tn_rem(s->kids, key, 0, KLEN, &v, &found);
  s->chk = mix(s->chk, found ? v : 9u);
}

/* restoring pair: insert a random key and remove the SAME key, so the trie
 * keeps its size (the key space is about a million keys, so a random key is
 * almost never present and an insert/remove pair -- unlike a remove of a key
 * that may not be there -- is exactly size preserving; see
 * benchmarks/bend/prefix_trie.bend) */
static inline void pt_pair_rm(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN];
  key_of(KLEN, r, key);
  s->kids = tn_ins(s->kids, key, 0, KLEN, r);
  s->chk = mix(s->chk, 1);
  uint32_t key2[KLEN], v = 0;
  key_of(KLEN, r, key2);
  int found = 0;
  s->kids = tn_rem(s->kids, key2, 0, KLEN, &v, &found);
  s->chk = mix(s->chk, found ? v : 9u);
}

static inline void pt_look(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN], v;
  key_of(KLEN, r, key);
  s->chk = mix(s->chk, tn_find(s->kids, key, 0, KLEN, &v) ? v : 9u);
}

static inline void pt_has(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN], v;
  key_of(KLEN, r, key);
  s->chk = mix(s->chk, tn_find(s->kids, key, 0, KLEN, &v) ? 1u : 0u);
}

static inline void pt_pre(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[2];
  key_of(2, r, key);
  s->chk = fold_pe(s->kids, key, 0, 2, 0, s->chk);
}

static inline void pt_lp(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t key[KLEN], v = 0;
  key_of(KLEN, r, key);
  uint32_t len = tn_lp(s->kids, key, 0, KLEN, 0, &v);
  if (len) {
    uint32_t c = s->chk;
    for (uint32_t i = 0; i < len; i++) c = mix(c, key[i]);
    s->chk = mix(c, v);
  } else if (s->has_root) {
    s->chk = mix(s->chk, s->root_val);
  } else {
    s->chk = mix(s->chk, 9);
  }
}

static inline void pt_new(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, 0);
}

static inline void pt_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t fold_all(const St *s, uint32_t c) {
  if (s->has_root) c = mix(c, s->root_val);
  return fold_ent(s->kids, 0, c);
}

static uint32_t round_pt(uint32_t op, uint32_t size, uint32_t count,
                       uint32_t nulls, uint32_t seed) {
  tn_used = 0;
  tn_free = NULL;
  St s;
  pt_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) pt_ins(&s);
  s.chk = fold_all(&s, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_ins(sp); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_look(sp); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_rm(sp); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_has(sp); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_pre(sp); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_lp(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_new(sp); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_pair_rm(sp); } break;
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); pt_null(sp); } break;
  }
  /* the value-stream steps of this region: every region runs the same
   * total number of loop iterations, so the loop barrier and the
   * argument generation cancel in the differences */
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); pt_null(sp); }
  /* size-independent drain: sixteen lookups from the same value stream */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) pt_look(&s);
  return s.chk;
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024 * 1024);
  tn_init(8ull * 1024ull * 1024ull);
  BENCH_REGIONS(round_pt)
  return 0;
}
