/* Optimized C reference for the LRU cache (benchmarks/bend/lru.bend over
 * src/lru/fast.bend).
 *
 * Design -- the standard efficient LRU:
 *   - slot arena: key[], val[], dl[] (deadline), prev[], next[] indexed by a
 *     uint32 slot; the recency order is an INTRUSIVE DOUBLY LINKED LIST
 *     threaded through prev/next (head = oldest, tail = newest), so detach,
 *     touch, evict and remove are O(1); released slots go on a free list
 *     chained through next[] and are reused before fresh slots;
 *   - lookup: an open-addressing hash table (linear probing, power-of-two
 *     size, load <= 1/2, backward-shift deletion so there are no tombstones)
 *     whose buckets hold the key AND its slot, so a probe touches one cache
 *     line and never dereferences the arena;
 *   - the arena and the table grow geometrically as entries arrive (the
 *     capacity is an upper bound, not a preallocation), purge is O(table)
 *     memset and resets the arena cursor, resize evicts the oldest entries.
 *
 * Keys are uint32 values i; the Bend key is the one-character String
 * Chr{65536 + i} (a valid Unicode scalar for every benchmark size), a
 * bijective image of the same 32-bit identity. There is no partially initialized key
 * buffer anywhere (the rejected reference's key_of/memcpy defect cannot
 * occur): every bucket and slot field that is read has been written.
 *
 * Semantics match src/lru/fast.bend exactly (docs/C_EQUIVALENCE.md):
 * five 64-bit metrics (inserts, evictions, removals, hits, misses), get
 * touches and counts a hit or a miss, peek/contains neither touch nor count,
 * an expired entry found by a read is removed (a removal) and reads as a
 * miss, add replaces in place (touch, inserts++) or inserts after evicting
 * the oldest when full, purge clears entries and metrics, resize(0) fails,
 * keys first drops the expired oldest prefix, new rejects 0 and 0xFFFFFFFF.
 * The benchmark never sets a lifetime, so every deadline is 0 (immortal),
 * but the check is performed on every read exactly as the Bend side does.
 *
 * The driver contract (selectors, draws, checksum folds) is documented in
 * benchmarks/bend/lru.bend; this file performs the identical work.
 */
#include "common.h"

#define NIL 0xFFFFFFFFu

typedef struct {
  uint32_t key;
  uint32_t slot; /* NIL = empty bucket */
} Bucket;

typedef struct {
  uint32_t cap, n, fresh, size; /* size = slots allocated */
  int64_t life;
  uint64_t inserts, evictions, removals, hits, misses;
  uint32_t head, tail, free;
  uint32_t *key, *val, *prev, *next;
  int64_t *dl;
  Bucket *tab;
  uint32_t tbits; /* table has 1 << tbits buckets */
} Lru;

typedef struct {
  uint32_t rng, chk, o;
  Lru c;
  uint32_t *out; /* keys() output buffer, capacity >= size */
} St;

/* ---- hash table ---- */

static inline uint32_t hash_of(uint32_t k, uint32_t bits) {
  return (k * 0x9E3779B1u) >> (32u - bits);
}

static Bucket *new_table(uint32_t bits) {
  size_t nb = (size_t)1 << bits;
  Bucket *t = (Bucket *)arena_alloc(nb * sizeof(Bucket));
  for (size_t i = 0; i < nb; i++) { t[i].key = 0; t[i].slot = NIL; }
  return t;
}

static inline uint32_t tab_find(const Lru *c, uint32_t k) {
  uint32_t mask = (1u << c->tbits) - 1u;
  for (uint32_t i = hash_of(k, c->tbits);; i = (i + 1u) & mask) {
    const Bucket *b = &c->tab[i];
    if (b->slot == NIL) return NIL;
    if (b->key == k) return b->slot;
  }
}

static inline void tab_put_raw(Bucket *t, uint32_t bits, uint32_t k, uint32_t s) {
  uint32_t mask = (1u << bits) - 1u;
  uint32_t i = hash_of(k, bits);
  while (t[i].slot != NIL) i = (i + 1u) & mask;
  t[i].key = k;
  t[i].slot = s;
}

static void tab_grow(Lru *c) {
  uint32_t bits = c->tbits + 1u;
  Bucket *t = new_table(bits);
  for (uint32_t s = c->head; s != NIL; s = c->next[s]) tab_put_raw(t, bits, c->key[s], s);
  c->tab = t;
  c->tbits = bits;
}

/* insert a key known to be absent; keeps load <= 1/2 */
static inline void tab_insert(Lru *c, uint32_t k, uint32_t s) {
  if (2u * (c->n + 1u) > (1u << c->tbits)) tab_grow(c);
  tab_put_raw(c->tab, c->tbits, k, s);
}

/* backward-shift deletion of a key known to be present */
static inline void tab_delete(Lru *c, uint32_t k) {
  uint32_t mask = (1u << c->tbits) - 1u;
  uint32_t i = hash_of(k, c->tbits);
  while (c->tab[i].key != k || c->tab[i].slot == NIL) i = (i + 1u) & mask;
  uint32_t j = i;
  for (;;) {
    j = (j + 1u) & mask;
    if (c->tab[j].slot == NIL) break;
    uint32_t h = hash_of(c->tab[j].key, c->tbits);
    /* move j back to i unless its home h lies cyclically in (i, j] */
    if (((j - h) & mask) >= ((j - i) & mask)) {
      c->tab[i] = c->tab[j];
      i = j;
    }
  }
  c->tab[i].slot = NIL;
  c->tab[i].key = 0;
}

/* ---- recency list ---- */

static inline void unlink_slot(Lru *c, uint32_t s) {
  uint32_t p = c->prev[s], q = c->next[s];
  if (p == NIL) c->head = q; else c->next[p] = q;
  if (q == NIL) c->tail = p; else c->prev[q] = p;
}

static inline void link_tail(Lru *c, uint32_t s) {
  c->prev[s] = c->tail;
  c->next[s] = NIL;
  if (c->tail == NIL) c->head = s; else c->next[c->tail] = s;
  c->tail = s;
}

static inline void touch(Lru *c, uint32_t s) {
  if (s == c->tail) return;
  unlink_slot(c, s);
  link_tail(c, s);
}

/* ---- construction / growth ---- */

static void lru_init(Lru *c, uint32_t cap) {
  c->cap = cap;
  c->n = 0;
  c->fresh = 0;
  c->size = 1;
  c->life = 0;
  c->inserts = c->evictions = c->removals = c->hits = c->misses = 0;
  c->head = c->tail = c->free = NIL;
  c->key = (uint32_t *)arena_alloc(sizeof(uint32_t));
  c->val = (uint32_t *)arena_alloc(sizeof(uint32_t));
  c->prev = (uint32_t *)arena_alloc(sizeof(uint32_t));
  c->next = (uint32_t *)arena_alloc(sizeof(uint32_t));
  c->dl = (int64_t *)arena_alloc(sizeof(int64_t));
  c->tbits = 1;
  c->tab = new_table(c->tbits);
}

/* the retained constructor's validation (new(cap) = new_with_size(cap, cap)):
 * capacity 0 and the reserved size 0xFFFFFFFF are rejected */
static int lru_new(Lru *c, uint32_t cap) {
  if (cap == 0 || cap == 0xFFFFFFFFu) return 0;
  lru_init(c, cap);
  return 1;
}

static void *regrow(void *old, size_t used, size_t bytes) {
  void *p = arena_alloc(bytes);
  memcpy(p, old, used);
  return p;
}

static void grow_slots(Lru *c) {
  size_t n = c->size, m = 2u * n;
  c->key = (uint32_t *)regrow(c->key, n * sizeof(uint32_t), m * sizeof(uint32_t));
  c->val = (uint32_t *)regrow(c->val, n * sizeof(uint32_t), m * sizeof(uint32_t));
  c->prev = (uint32_t *)regrow(c->prev, n * sizeof(uint32_t), m * sizeof(uint32_t));
  c->next = (uint32_t *)regrow(c->next, n * sizeof(uint32_t), m * sizeof(uint32_t));
  c->dl = (int64_t *)regrow(c->dl, n * sizeof(int64_t), m * sizeof(int64_t));
  c->size = (uint32_t)m;
}

/* ---- operations ---- */

static inline int64_t deadline_of(const Lru *c, int64_t now) {
  return c->life == 0 ? 0 : now + c->life / 1000000; /* ns -> ms */
}

static inline int expired(int64_t d, int64_t now) { return d != 0 && d <= now; }

/* remove live slot s; evict = 1 counts an eviction, 0 a removal */
static inline uint32_t remove_slot(Lru *c, uint32_t s, int evict) {
  uint32_t v = c->val[s];
  tab_delete(c, c->key[s]);
  unlink_slot(c, s);
  c->next[s] = c->free;
  c->free = s;
  c->n--;
  if (evict) c->evictions++; else c->removals++;
  return v;
}

/* returns 1 when an entry was evicted */
static inline uint32_t lru_add(Lru *c, uint32_t k, uint32_t v, int64_t now) {
  int64_t d = deadline_of(c, now);
  uint32_t s = tab_find(c, k);
  if (s != NIL) {
    c->val[s] = v;
    c->dl[s] = d;
    touch(c, s);
    c->inserts++;
    return 0;
  }
  uint32_t ev = 0;
  if (c->cap <= c->n) { remove_slot(c, c->head, 1); ev = 1; }
  if (c->free != NIL) {
    s = c->free;
    c->free = c->next[s];
  } else {
    if (c->fresh >= c->size) grow_slots(c);
    s = c->fresh++;
  }
  c->key[s] = k;
  c->val[s] = v;
  c->dl[s] = d;
  tab_insert(c, k, s);
  c->n++;
  c->inserts++;
  link_tail(c, s);
  return ev;
}

/* *found = 1 and the value on a live hit */
static inline uint32_t lru_read(Lru *c, uint32_t k, int64_t now, int tracked, int *found) {
  uint32_t s = tab_find(c, k);
  *found = 0;
  if (s == NIL) {
    if (tracked) c->misses++;
    return 0;
  }
  if (expired(c->dl[s], now)) {
    remove_slot(c, s, 0);
    if (tracked) c->misses++;
    return 0;
  }
  if (tracked) { c->hits++; touch(c, s); }
  *found = 1;
  return c->val[s];
}

static inline uint32_t lru_remove(Lru *c, uint32_t k, int *found) {
  uint32_t s = tab_find(c, k);
  *found = s != NIL;
  return s == NIL ? 0 : remove_slot(c, s, 0);
}

static inline uint32_t lru_purge(Lru *c) {
  uint32_t n = c->n;
  size_t nb = (size_t)1 << c->tbits;
  for (size_t i = 0; i < nb; i++) { c->tab[i].key = 0; c->tab[i].slot = NIL; }
  c->n = 0;
  c->fresh = 0;
  c->head = c->tail = c->free = NIL;
  c->inserts = c->evictions = c->removals = c->hits = c->misses = 0;
  return n;
}

/* returns 0 on failure (capacity 0), else 1 with *ev evictions */
static inline int lru_resize(Lru *c, uint32_t cap, uint32_t *ev) {
  if (cap == 0) return 0;
  c->cap = cap;
  uint32_t e = 0;
  while (c->cap < c->n) { remove_slot(c, c->head, 1); e++; }
  *ev = e;
  return 1;
}

/* the keys, oldest first, into out[]; returns how many. As the retained
 * Keys, the oldest EXPIRED prefix is removed first (each a removal),
 * stopping at the first immortal or live oldest entry. */
static inline uint32_t lru_keys(Lru *c, uint32_t *out, int64_t now) {
  while (c->head != NIL && expired(c->dl[c->head], now)) remove_slot(c, c->head, 0);
  uint32_t m = 0;
  for (uint32_t s = c->head; s != NIL; s = c->next[s]) out[m++] = c->key[s];
  return m;
}

/* ---- the driver (contract in benchmarks/bend/lru.bend) ---- */

static inline uint32_t capof(uint32_t size) { return size == 0 ? 1u : size; }

static inline uint32_t draw(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  return r % (size + 1u);
}

static inline uint32_t fold_keys(St *s, uint32_t c) {
  uint32_t m = lru_keys(&s->c, s->out, 0);
  for (uint32_t j = 0; j < m; j++) c = mix(c, s->out[j]);
  return c;
}

static inline void refill(Lru *c, uint32_t k, uint32_t at, uint32_t m) {
  for (uint32_t j = 0; j < k; j++) {
    lru_add(c, at, at + 1u, 0);
    at = at + 1u < m ? at + 1u : 0u;
  }
}

static inline void op_add(St *s, uint32_t size) {
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, lru_add(&s->c, i, i + 1u, 0));
}

static inline void op_read(St *s, uint32_t size, int tracked) {
  int f;
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, lru_read(&s->c, i, 0, tracked, &f));
}

static inline void op_contains(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  lru_read(&s->c, i, 0, 0, &f);
  s->chk = mix(s->chk, (uint32_t)f);
}

static inline void op_remove(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, lru_remove(&s->c, i, &f));
}

static inline void op_purge(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, lru_purge(&s->c));
}

static inline uint32_t rs_code(uint32_t c, uint32_t t, int ok, uint32_t ev) {
  return ok ? mix(mix(c, t), ev) : mix(c, 0xFFFFFFFFu);
}

static inline void op_resize(St *s, uint32_t size) {
  uint32_t t = draw(s, size), ev = 0;
  int ok = lru_resize(&s->c, t, &ev);
  s->chk = rs_code(s->chk, t, ok, ev);
}

static inline void op_keys(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_keys(s, s->chk);
}

static inline void op_len(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->c.n);
}

static inline void op_new(St *s, uint32_t size) {
  s->rng = lcg(s->rng);
  Lru g;
  Lru *gp = &g;
  int ok = lru_new(gp, size);
  keep(gp);
  s->chk = ok ? mix(mix(s->chk, gp->cap), gp->n) : mix(s->chk, 0xFFFFFFFFu);
}

static inline void op_remove_add(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  uint32_t v = lru_remove(&s->c, i, &f);
  s->chk = mix(mix(s->chk, v), lru_add(&s->c, i, i + 1u, 0));
}

static inline void op_purge_refill(St *s, uint32_t size) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, lru_purge(&s->c));
  refill(&s->c, size, 0, capof(size));
  s->o = 0;
}

static inline void op_resize_back(St *s, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  uint32_t m = capof(size);
  uint32_t t = 1u + r % m, ev = 0, ev2 = 0;
  int ok = lru_resize(&s->c, t, &ev);
  s->chk = rs_code(s->chk, t, ok, ev);
  int ok2 = lru_resize(&s->c, m, &ev2);
  s->chk = mix(s->chk, ok2 ? ev2 : 0u);
  uint32_t e = ok ? ev : 0u;
  refill(&s->c, e, s->o, m);
  s->o = (s->o + e) % m;
}


/* ---- selectors 13-17: the rest of the public API (contract in
 * benchmarks/bend/lru.bend) ---- */

static inline void op_capacity(St *s) {
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, s->c.cap);
}

static inline void op_set_lifetime(St *s, uint32_t size) {
  uint32_t ns = draw(s, size);
  s->c.life = (int64_t)ns;
  s->chk = mix(mix(s->chk, ns), s->c.n);
}

static inline uint32_t fold_metrics(const Lru *c, uint32_t k) {
  uint64_t ms[5] = {c->inserts, c->evictions, c->removals, c->hits, c->misses};
  for (int i = 0; i < 5; i++) k = mix(mix(k, (uint32_t)ms[i]), (uint32_t)(ms[i] >> 32));
  return k;
}

static inline void op_metrics(St *s) {
  s->rng = lcg(s->rng);
  s->chk = fold_metrics(&s->c, s->chk);
}

/* add key i with the round's one millisecond lifetime at stamp 0 (deadline 1),
 * then read it back at stamp 2: the read finds it EXPIRED, drops it (a
 * removal) and answers a miss */
static inline void op_expiry(St *s, uint32_t size) {
  int f;
  uint32_t i = draw(s, size);
  s->chk = mix(s->chk, lru_add(&s->c, i, i + 1u, 0));
  s->chk = mix(s->chk, lru_read(&s->c, i, 2, 1, &f));
}

/* isolated removal of the distinct, present key (o + j) mod cap */
static inline void op_remove_seq(St *s, uint32_t size) {
  int f;
  uint32_t i = s->o, m = capof(size);
  s->rng = lcg(s->rng);
  s->chk = mix(s->chk, lru_remove(&s->c, i, &f));
  s->o = i + 1u < m ? i + 1u : 0u;
}


/* ---- selectors 18/19: ISOLATED purge and resize over a prepared pool ----
 *
 * Both regions build the SAME pool of 2 * count independent full caches (the
 * pool size is the row's `count`, not the region's k), so the preparation
 * cancels in A - B; region A then destroys 2k of them and region B k, and the
 * difference is exactly k destructive calls, each on its own full cache.
 * Caches a region does not reach are simply left in the round's arena. */

typedef struct {
  Lru *v;
  uint32_t used;
  uint32_t have;
} Pool;

/* the row's `count` from argv. round_lru only receives the REGION's count
 * (2k, k or 0), and selectors 18/19 must build the same pool in all three
 * regions, so main records the row's count here before the regions run. */
static uint32_t g_pool = 0;

static void pool_build(Pool *pl, uint32_t m, uint32_t size) {
  pl->v = (Lru *)arena_alloc((size_t)m * sizeof(Lru));
  pl->used = 0;
  pl->have = m;
  for (uint32_t j = 0; j < m; j++) {
    lru_init(&pl->v[j], capof(size));
    refill(&pl->v[j], size, 0, capof(size));
  }
}

static inline void op_pool_purge(St *s, Pool *pl) {
  s->rng = lcg(s->rng);
  if (pl->used == pl->have) { s->chk = mix(s->chk, 0xFFFFFFFFu); return; }
  s->chk = mix(s->chk, lru_purge(&pl->v[pl->used++]));
}

static inline void op_pool_resize(St *s, Pool *pl, uint32_t size) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  if (pl->used == pl->have) { s->chk = mix(s->chk, 0xFFFFFFFFu); return; }
  uint32_t t = 1u + r % capof(size), ev = 0;
  int ok = lru_resize(&pl->v[pl->used++], t, &ev);
  s->chk = rs_code(s->chk, t, ok, ev);
}

static inline void op_null(St *s) {
  uint32_t r = lcg(s->rng);
  s->rng = r;
  s->chk = mix(s->chk, r);
}

static uint32_t round_lru(uint32_t op, uint32_t size, uint32_t count,
                          uint32_t nulls, uint32_t seed) {
  uint32_t pool = g_pool; /* the ROW's count: region independent, see main */
  arena_reset();
  St s;
  s.rng = seed;
  s.chk = 0;
  s.o = 0;
  s.out = (uint32_t *)arena_alloc((size_t)capof(size) * sizeof(uint32_t));
  lru_init(&s.c, capof(size));
  refill(&s.c, size, 0, capof(size));
  s.chk = fold_keys(&s, s.chk); /* settle */
  St *sp = &s;
  keep(sp);
  switch (op) {
    case 0: for (uint32_t i = 0; i < count; i++) { keep(sp); op_add(sp, size); } break;
    case 1: for (uint32_t i = 0; i < count; i++) { keep(sp); op_read(sp, size, 1); } break;
    case 2: for (uint32_t i = 0; i < count; i++) { keep(sp); op_read(sp, size, 0); } break;
    case 3: for (uint32_t i = 0; i < count; i++) { keep(sp); op_contains(sp, size); } break;
    case 4: for (uint32_t i = 0; i < count; i++) { keep(sp); op_remove(sp, size); } break;
    case 5: for (uint32_t i = 0; i < count; i++) { keep(sp); op_purge(sp); } break;
    case 6: for (uint32_t i = 0; i < count; i++) { keep(sp); op_resize(sp, size); } break;
    case 7: for (uint32_t i = 0; i < count; i++) { keep(sp); op_keys(sp); } break;
    case 8: for (uint32_t i = 0; i < count; i++) { keep(sp); op_len(sp); } break;
    case 9: for (uint32_t i = 0; i < count; i++) { keep(sp); op_new(sp, size); } break;
    case 10: for (uint32_t i = 0; i < count; i++) { keep(sp); op_remove_add(sp, size); } break;
    case 11: for (uint32_t i = 0; i < count; i++) { keep(sp); op_purge_refill(sp, size); } break;
    case 12: for (uint32_t i = 0; i < count; i++) { keep(sp); op_resize_back(sp, size); } break;
    case 13: for (uint32_t i = 0; i < count; i++) { keep(sp); op_capacity(sp); } break;
    case 14: for (uint32_t i = 0; i < count; i++) { keep(sp); op_set_lifetime(sp, size); } break;
    case 15: for (uint32_t i = 0; i < count; i++) { keep(sp); op_metrics(sp); } break;
    case 16: s.c.life = 1000000; for (uint32_t i = 0; i < count; i++) { keep(sp); op_expiry(sp, size); } break;
    case 17: for (uint32_t i = 0; i < count; i++) { keep(sp); op_remove_seq(sp, size); } break;
    case 18: { Pool pl; pool_build(&pl, 2u * pool, size);
               for (uint32_t i = 0; i < count; i++) { keep(sp); op_pool_purge(sp, &pl); } break; }
    case 19: { Pool pl; pool_build(&pl, 2u * pool, size);
               for (uint32_t i = 0; i < count; i++) { keep(sp); op_pool_resize(sp, &pl, size); } break; }
    default: for (uint32_t i = 0; i < count; i++) { keep(sp); op_null(sp); } break;
  }
  for (uint32_t i = 0; i < nulls; i++) { keep(sp); op_null(sp); }
  /* size-independent drain: sixteen peeks, the length, the five metrics */
  s.chk = mix(s.chk, s.rng);
  for (int i = 0; i < 16; i++) op_read(&s, size, 0);
  return fold_metrics(&s.c, mix(s.chk, s.c.n));
}

/* BENCH_MAIN(round_lru, ...) expanded, with the one extra line that records
 * the row's count for the pooled selectors 18/19 (see g_pool above). */
int main(int argc, char **argv) {
  bench_args a = parse_args(argc, argv);
  arena_init(2048ull * 1024ull * 1024ull);
  g_pool = a.count;
  BENCH_REGIONS(round_lru)
  return 0;
}
