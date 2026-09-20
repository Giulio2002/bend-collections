/* Optimized C reference for the 2-3 tree ordered map of
 * src/balanced_search_tree.bend (U32 keys ordered by U32.cmp, U32 values).
 *
 * Same algorithm and representation: every internal node holds two or three
 * children and one or two entries, and all leaves sit at the same depth.
 * Insertion splits an overflowing node upwards (the TI/OF "up" cases of the
 * Bend source); deletion repairs an underflow by borrowing from or merging
 * with a sibling (the node21..node33 cases) and replaces a deleted internal
 * entry with the minimum of the subtree to its right (split_min). Queries are
 * the same descents: find, min, max, lower_bound, the pruned range walk and
 * the in-order entry walk.
 *
 * Nodes are mutated in place and reused: each Bend helper consumes the node it
 * destructures, so reusing that node is exactly what a linear implementation
 * does, and it keeps the reference free of allocator noise.
 */
#ifndef BENCH_TWOTHREE_H
#define BENCH_TWOTHREE_H

#include "common.h"

typedef struct TT {
  uint8_t kind; /* 2 or 3 */
  uint32_t k1, k2;
  uint64_t v1, v2;
  struct TT *a, *b, *c;
} TT;

static TT *tt_pool = NULL;
static TT *tt_free = NULL;
static size_t tt_cap = 0, tt_used = 0;

static void tt_init_pool(size_t count) {
  tt_pool = (TT *)malloc(sizeof(TT) * count);
  if (!tt_pool) {
    fprintf(stderr, "2-3 node pool allocation failed\n");
    exit(2);
  }
  tt_cap = count;
  tt_used = 0;
  tt_free = NULL;
}

static void tt_reset_pool(void) {
  tt_used = 0;
  tt_free = NULL;
}

static inline TT *tt_alloc(void) {
  TT *n = tt_free;
  if (n) {
    tt_free = n->a;
  } else {
    if (tt_used == tt_cap) {
      fprintf(stderr, "2-3 node pool exhausted (%zu)\n", tt_cap);
      exit(2);
    }
    n = &tt_pool[tt_used++];
  }
  n->kind = 2;
  n->a = n->b = n->c = NULL;
  return n;
}

static inline void tt_release(TT *n) {
  n->a = tt_free;
  tt_free = n;
}

static inline TT *tt_node2(TT *a, uint32_t k, uint64_t v, TT *b) {
  TT *n = tt_alloc();
  n->kind = 2;
  n->k1 = k;
  n->v1 = v;
  n->a = a;
  n->b = b;
  return n;
}

/* ---- insertion ---- */

typedef struct {
  int of;          /* 1 = the subtree overflowed */
  TT *t;           /* of == 0 */
  TT *l, *r;       /* of == 1 */
  uint32_t k;
  uint64_t v;
} TTIns;

static TTIns tt_ins(TT *t, uint32_t k, uint64_t v) {
  TTIns out;
  if (!t) {
    out.of = 1;
    out.l = NULL;
    out.r = NULL;
    out.k = k;
    out.v = v;
    return out;
  }
  if (t->kind == 2) {
    if (k < t->k1) {
      TTIns s = tt_ins(t->a, k, v);
      if (!s.of) {
        t->a = s.t;
      } else { /* up2l: Node3{s.l, s.kv, s.r, e, b} */
        t->kind = 3;
        t->k2 = t->k1;
        t->v2 = t->v1;
        t->k1 = s.k;
        t->v1 = s.v;
        t->c = t->b;
        t->b = s.r;
        t->a = s.l;
      }
    } else if (k == t->k1) {
      t->v1 = v;
    } else {
      TTIns s = tt_ins(t->b, k, v);
      if (!s.of) {
        t->b = s.t;
      } else { /* up2r: Node3{a, e, s.l, s.kv, s.r} */
        t->kind = 3;
        t->k2 = s.k;
        t->v2 = s.v;
        t->c = s.r;
        t->b = s.l;
      }
    }
    out.of = 0;
    out.t = t;
    return out;
  }
  /* kind == 3 */
  if (k < t->k1) {
    TTIns s = tt_ins(t->a, k, v);
    if (!s.of) {
      t->a = s.t;
      out.of = 0;
      out.t = t;
      return out;
    }
    TT *left = tt_node2(s.l, s.k, s.v, s.r);
    out.of = 1;
    out.l = left;
    out.k = t->k1;
    out.v = t->v1;
    t->kind = 2;
    t->k1 = t->k2;
    t->v1 = t->v2;
    t->a = t->b;
    t->b = t->c;
    out.r = t;
    return out;
  }
  if (k == t->k1) {
    t->v1 = v;
    out.of = 0;
    out.t = t;
    return out;
  }
  if (k < t->k2) {
    TTIns s = tt_ins(t->b, k, v);
    if (!s.of) {
      t->b = s.t;
      out.of = 0;
      out.t = t;
      return out;
    }
    TT *left = tt_node2(t->a, t->k1, t->v1, s.l);
    out.of = 1;
    out.l = left;
    out.k = s.k;
    out.v = s.v;
    t->kind = 2;
    t->a = s.r;
    t->k1 = t->k2;
    t->v1 = t->v2;
    t->b = t->c;
    out.r = t;
    return out;
  }
  if (k == t->k2) {
    t->v2 = v;
    out.of = 0;
    out.t = t;
    return out;
  }
  {
    TTIns s = tt_ins(t->c, k, v);
    if (!s.of) {
      t->c = s.t;
      out.of = 0;
      out.t = t;
      return out;
    }
    TT *right = tt_node2(s.l, s.k, s.v, s.r);
    out.of = 1;
    out.k = t->k2;
    out.v = t->v2;
    t->kind = 2;
    out.l = t;
    out.r = right;
    return out;
  }
}

static TT *tt_insert(TT *t, uint32_t k, uint64_t v) {
  TTIns s = tt_ins(t, k, v);
  if (!s.of) return s.t;
  return tt_node2(s.l, s.k, s.v, s.r);
}

/* ---- deletion ---- */

typedef struct {
  int uf; /* 1 = the subtree lost a level */
  TT *t;
} TTDel;

static inline TTDel tt_td(TT *t) { TTDel d; d.uf = 0; d.t = t; return d; }
static inline TTDel tt_uf(TT *t) { TTDel d; d.uf = 1; d.t = t; return d; }

/* the parent node `p` is reused for the result */
static TTDel tt_node21(TT *p, TTDel u, TT *r) {
  if (!u.uf) {
    p->kind = 2;
    p->a = u.t;
    p->b = r;
    return tt_td(p);
  }
  if (r && r->kind == 2) { /* UF{l} Node2{r1,x,r2} -> UF{Node3{l,e,r1,x,r2}} */
    p->kind = 3;
    p->k2 = r->k1;
    p->v2 = r->v1;
    p->a = u.t;
    p->b = r->a;
    p->c = r->b;
    tt_release(r);
    return tt_uf(p);
  }
  if (r && r->kind == 3) { /* TD{Node2{Node2{l,e,r1}, x, Node2{r2,y,r3}}} */
    TT *left = tt_node2(u.t, p->k1, p->v1, r->a);
    TT *right = tt_node2(r->b, r->k2, r->v2, r->c);
    p->kind = 2;
    p->k1 = r->k1;
    p->v1 = r->v1;
    p->a = left;
    p->b = right;
    tt_release(r);
    return tt_td(p);
  }
  p->kind = 2;
  p->a = u.t;
  p->b = NULL;
  return tt_td(p);
}

static TTDel tt_node22(TT *p, TT *l, TTDel u) {
  if (!u.uf) {
    p->kind = 2;
    p->a = l;
    p->b = u.t;
    return tt_td(p);
  }
  if (l && l->kind == 2) { /* UF{Node3{l1,x,l2,e,r}} */
    p->kind = 3;
    p->k2 = p->k1;
    p->v2 = p->v1;
    p->k1 = l->k1;
    p->v1 = l->v1;
    p->a = l->a;
    p->b = l->b;
    p->c = u.t;
    tt_release(l);
    return tt_uf(p);
  }
  if (l && l->kind == 3) { /* TD{Node2{Node2{l1,x,l2}, y, Node2{l3,e,r}}} */
    TT *left = tt_node2(l->a, l->k1, l->v1, l->b);
    TT *right = tt_node2(l->c, p->k1, p->v1, u.t);
    p->kind = 2;
    p->k1 = l->k2;
    p->v1 = l->v2;
    p->a = left;
    p->b = right;
    tt_release(l);
    return tt_td(p);
  }
  p->kind = 2;
  p->a = NULL;
  p->b = u.t;
  return tt_td(p);
}

static TTDel tt_node31(TT *p, TTDel u, TT *m, TT *r) {
  if (!u.uf) {
    p->kind = 3;
    p->a = u.t;
    p->b = m;
    p->c = r;
    return tt_td(p);
  }
  if (m && m->kind == 2) { /* TD{Node2{Node3{l,e1,m1,x,m2}, e2, r}} */
    TT *left = tt_alloc();
    left->kind = 3;
    left->k1 = p->k1;
    left->v1 = p->v1;
    left->k2 = m->k1;
    left->v2 = m->v1;
    left->a = u.t;
    left->b = m->a;
    left->c = m->b;
    p->kind = 2;
    p->k1 = p->k2;
    p->v1 = p->v2;
    p->a = left;
    p->b = r;
    tt_release(m);
    return tt_td(p);
  }
  if (m && m->kind == 3) { /* TD{Node3{Node2{l,e1,m1}, x, Node2{m2,y,m3}, e2, r}} */
    TT *left = tt_node2(u.t, p->k1, p->v1, m->a);
    TT *mid = tt_node2(m->b, m->k2, m->v2, m->c);
    p->kind = 3;
    p->k1 = m->k1;
    p->v1 = m->v1;
    p->a = left;
    p->b = mid;
    p->c = r;
    tt_release(m);
    return tt_td(p);
  }
  p->kind = 3;
  p->a = u.t;
  p->b = NULL;
  p->c = r;
  return tt_td(p);
}

static TTDel tt_node32(TT *p, TT *l, TTDel u, TT *r) {
  if (!u.uf) {
    p->kind = 3;
    p->a = l;
    p->b = u.t;
    p->c = r;
    return tt_td(p);
  }
  if (r && r->kind == 2) { /* TD{Node2{l, e1, Node3{m, e2, r1, x, r2}}} */
    TT *right = tt_alloc();
    right->kind = 3;
    right->k1 = p->k2;
    right->v1 = p->v2;
    right->k2 = r->k1;
    right->v2 = r->v1;
    right->a = u.t;
    right->b = r->a;
    right->c = r->b;
    p->kind = 2;
    p->a = l;
    p->b = right;
    tt_release(r);
    return tt_td(p);
  }
  if (r && r->kind == 3) { /* TD{Node3{l, e1, Node2{m,e2,r1}, x, Node2{r2,y,r3}}} */
    TT *mid = tt_node2(u.t, p->k2, p->v2, r->a);
    TT *right = tt_node2(r->b, r->k2, r->v2, r->c);
    p->kind = 3;
    p->k2 = r->k1;
    p->v2 = r->v1;
    p->a = l;
    p->b = mid;
    p->c = right;
    tt_release(r);
    return tt_td(p);
  }
  p->kind = 3;
  p->a = l;
  p->b = u.t;
  p->c = NULL;
  return tt_td(p);
}

static TTDel tt_node33(TT *p, TT *l, TT *m, TTDel u) {
  if (!u.uf) {
    p->kind = 3;
    p->a = l;
    p->b = m;
    p->c = u.t;
    return tt_td(p);
  }
  if (m && m->kind == 2) { /* TD{Node2{l, e1, Node3{m1,x,m2,e2,r}}} */
    TT *right = tt_alloc();
    right->kind = 3;
    right->k1 = m->k1;
    right->v1 = m->v1;
    right->k2 = p->k2;
    right->v2 = p->v2;
    right->a = m->a;
    right->b = m->b;
    right->c = u.t;
    p->kind = 2;
    p->a = l;
    p->b = right;
    tt_release(m);
    return tt_td(p);
  }
  if (m && m->kind == 3) { /* TD{Node3{l, e1, Node2{m1,x,m2}, y, Node2{m3,e2,r}}} */
    TT *mid = tt_node2(m->a, m->k1, m->v1, m->b);
    TT *right = tt_node2(m->c, p->k2, p->v2, u.t);
    p->kind = 3;
    p->k2 = m->k2;
    p->v2 = m->v2;
    p->a = l;
    p->b = mid;
    p->c = right;
    tt_release(m);
    return tt_td(p);
  }
  p->kind = 3;
  p->a = l;
  p->b = NULL;
  p->c = u.t;
  return tt_td(p);
}

/* split_min: the smallest entry and the rest */
typedef struct {
  int some;
  uint32_t k;
  uint64_t v;
  TTDel rest;
} TTMin;

static TTMin tt_split_min(TT *t) {
  TTMin out;
  if (!t) {
    out.some = 0;
    return out;
  }
  if (t->kind == 2) {
    TTMin s = tt_split_min(t->a);
    if (!s.some) { /* SMSome{e, UF{r}} */
      out.some = 1;
      out.k = t->k1;
      out.v = t->v1;
      TT *r = t->b;
      tt_release(t);
      out.rest = tt_uf(r);
      return out;
    }
    out.some = 1;
    out.k = s.k;
    out.v = s.v;
    out.rest = tt_node21(t, s.rest, t->b);
    return out;
  }
  {
    TTMin s = tt_split_min(t->a);
    if (!s.some) { /* SMSome{e1, TD{Node2{m, e2, r}}} */
      out.some = 1;
      out.k = t->k1;
      out.v = t->v1;
      t->kind = 2;
      t->k1 = t->k2;
      t->v1 = t->v2;
      t->a = t->b;
      t->b = t->c;
      out.rest = tt_td(t);
      return out;
    }
    out.some = 1;
    out.k = s.k;
    out.v = s.v;
    out.rest = tt_node31(t, s.rest, t->b, t->c);
    return out;
  }
}

static TTDel tt_del(TT *t, uint32_t k) {
  if (!t) return tt_td(NULL);
  if (t->kind == 2) {
    if (k < t->k1) return tt_node21(t, tt_del(t->a, k), t->b);
    if (k == t->k1) {
      TTMin s = tt_split_min(t->b);
      if (!s.some) {
        TT *l = t->a;
        tt_release(t);
        return tt_uf(l);
      }
      t->k1 = s.k;
      t->v1 = s.v;
      return tt_node22(t, t->a, s.rest);
    }
    return tt_node22(t, t->a, tt_del(t->b, k));
  }
  if (k < t->k1) return tt_node31(t, tt_del(t->a, k), t->b, t->c);
  if (k == t->k1) {
    TTMin s = tt_split_min(t->b);
    if (!s.some) { /* TD{Node2{l, e2, r}} */
      t->kind = 2;
      t->k1 = t->k2;
      t->v1 = t->v2;
      t->b = t->c;
      return tt_td(t);
    }
    t->k1 = s.k;
    t->v1 = s.v;
    return tt_node32(t, t->a, s.rest, t->c);
  }
  if (k < t->k2) return tt_node32(t, t->a, tt_del(t->b, k), t->c);
  if (k == t->k2) {
    TTMin s = tt_split_min(t->c);
    if (!s.some) { /* TD{Node2{l, e1, m}} */
      t->kind = 2;
      return tt_td(t);
    }
    t->k2 = s.k;
    t->v2 = s.v;
    return tt_node33(t, t->a, t->b, s.rest);
  }
  return tt_node33(t, t->a, t->b, tt_del(t->c, k));
}

static TT *tt_remove(TT *t, uint32_t k) { return tt_del(t, k).t; }

/* ---- queries ---- */

static int tt_find(const TT *t, uint32_t k, uint64_t *out) {
  while (t) {
    if (k < t->k1) {
      t = t->a;
    } else if (k == t->k1) {
      *out = t->v1;
      return 1;
    } else if (t->kind == 2) {
      t = t->b;
    } else if (k < t->k2) {
      t = t->b;
    } else if (k == t->k2) {
      *out = t->v2;
      return 1;
    } else {
      t = t->c;
    }
  }
  return 0;
}

static int tt_min(const TT *t, uint32_t *k, uint64_t *v) {
  if (!t) return 0;
  while (t->a) t = t->a;
  *k = t->k1;
  *v = t->v1;
  return 1;
}

static int tt_max(const TT *t, uint32_t *k, uint64_t *v) {
  if (!t) return 0;
  while (1) {
    const TT *nxt = (t->kind == 2) ? t->b : t->c;
    if (!nxt) break;
    t = nxt;
  }
  if (t->kind == 2) {
    *k = t->k1;
    *v = t->v1;
  } else {
    *k = t->k2;
    *v = t->v2;
  }
  return 1;
}

/* first entry with key >= k */
static int tt_lower(const TT *t, uint32_t k, uint32_t *ok, uint64_t *ov) {
  int found = 0;
  while (t) {
    if (t->kind == 2) {
      if (t->k1 < k) {
        t = t->b;
      } else if (t->k1 == k) {
        *ok = t->k1;
        *ov = t->v1;
        return 1;
      } else {
        *ok = t->k1;
        *ov = t->v1;
        found = 1;
        t = t->a;
      }
    } else {
      if (t->k1 < k) {
        if (t->k2 < k) {
          t = t->c;
        } else if (t->k2 == k) {
          *ok = t->k2;
          *ov = t->v2;
          return 1;
        } else {
          *ok = t->k2;
          *ov = t->v2;
          found = 1;
          t = t->b;
        }
      } else if (t->k1 == k) {
        *ok = t->k1;
        *ov = t->v1;
        return 1;
      } else {
        *ok = t->k1;
        *ov = t->v1;
        found = 1;
        t = t->a;
      }
    }
  }
  return found;
}

/* pruned range walk: fold lo <= key < hi in key order */
static uint32_t tt_range(const TT *t, uint32_t lo, uint32_t hi, uint32_t c, int go) {
  if (!go || !t) return c;
  if (t->kind == 2) {
    c = tt_range(t->a, lo, hi, c, lo < t->k1);
    if (lo <= t->k1 && t->k1 < hi) c = mix(mix(c, t->k1), (uint32_t)t->v1);
    return tt_range(t->b, lo, hi, c, t->k1 < hi);
  }
  c = tt_range(t->a, lo, hi, c, lo < t->k1);
  if (lo <= t->k1 && t->k1 < hi) c = mix(mix(c, t->k1), (uint32_t)t->v1);
  c = tt_range(t->b, lo, hi, c, t->k1 < hi && lo < t->k2);
  if (lo <= t->k2 && t->k2 < hi) c = mix(mix(c, t->k2), (uint32_t)t->v2);
  return tt_range(t->c, lo, hi, c, t->k2 < hi);
}

static uint32_t tt_entries(const TT *t, uint32_t c) {
  if (!t) return c;
  c = tt_entries(t->a, c);
  c = mix(mix(c, t->k1), (uint32_t)t->v1);
  c = tt_entries(t->b, c);
  if (t->kind == 3) {
    c = mix(mix(c, t->k2), (uint32_t)t->v2);
    c = tt_entries(t->c, c);
  }
  return c;
}

static uint32_t tt_count(const TT *t) {
  if (!t) return 0;
  uint32_t n = (t->kind == 2) ? 1u : 2u;
  n += tt_count(t->a) + tt_count(t->b);
  if (t->kind == 3) n += tt_count(t->c);
  return n;
}

#endif
