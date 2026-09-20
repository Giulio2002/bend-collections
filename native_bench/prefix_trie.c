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

static TN *tn_rem(TN *t, const uint32_t *key, uint32_t i, uint32_t m) {
  if (!t) return NULL;
  if (key[i] < t->c) return t;
  if (key[i] > t->c) {
    t->next = tn_rem(t->next, key, i, m);
    return t;
  }
  if (i + 1 == m) {
    t->has = 0;
    return prune(t);
  }
  t->down = tn_rem(t->down, key, i + 1, m);
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
  uint32_t key[KLEN], v;
  key_of(KLEN, r, key);
  uint32_t code = 9;
  if (tn_find(s->kids, key, 0, KLEN, &v)) {
    s->kids = tn_rem(s->kids, key, 0, KLEN);
    code = v;
  }
  s->chk = mix(s->chk, code);
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

static uint32_t round_pt(uint32_t op, uint32_t size, uint32_t count, uint32_t seed) {
  tn_used = 0;
  tn_free = NULL;
  St s;
  pt_init(&s, seed);
  for (uint32_t i = 0; i < size; i++) pt_ins(&s);
  s.chk = fold_all(&s, s.chk); /* settle */
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) pt_ins(&s); break;
    case 1: for (uint32_t i = 0; i < count; i++) pt_look(&s); break;
    case 2: for (uint32_t i = 0; i < count; i++) pt_rm(&s); break;
    case 3: for (uint32_t i = 0; i < count; i++) pt_has(&s); break;
    case 4: for (uint32_t i = 0; i < count; i++) pt_pre(&s); break;
    case 5: for (uint32_t i = 0; i < count; i++) pt_lp(&s); break;
    case 6: for (uint32_t i = 0; i < count; i++) pt_new(&s); break;
    default: for (uint32_t i = 0; i < count; i++) pt_null(&s); break;
  }
  /* size-independent drain: sixteen lookups from the same value stream */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) pt_look(&s);
  return s.chk;
}

int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(1024 * 1024);
  tn_init(8ull * 1024ull * 1024ull);
  uint32_t acc_a = 0, acc_b = 0;
  uint64_t t0 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_a = mix(acc_a, round_pt(a.op, a.size, a.count, a.seed + p));
  uint64_t t1 = now_ns();
  uint64_t t2 = now_ns();
  for (uint32_t p = a.reps; p-- > 0;)
    acc_b = mix(acc_b, round_pt(NULL_OP, a.size, a.count, a.seed + p));
  uint64_t t3 = now_ns();
  emit(acc_a, acc_b, t1 - t0, t3 - t2);
  return 0;
}
