/* Optimized C reference for the RED-BLACK BINARY search tree ordered map of
 * src/balanced_search_tree.bend (U32 keys ordered by U32.cmp, U32 values).
 *
 * Same algorithm and representation: every node has a colour and exactly two
 * children, the root and the empty leaves (NULL) are black, no red node has a
 * red child, and every root-to-leaf path holds the same number of black
 * nodes.
 *
 *   insert  Okasaki: the new node is red and `rb_balance` repairs the single
 *           red-red edge below a black node with the four classic rotations,
 *           in the same order the Bend source tries them (bal_ll, bal_lr,
 *           bal_rl, bal_rr); the root is blackened afterwards.
 *   remove  the conventional functional fixup: rb_del returns TD (the black
 *           height is unchanged) or UF (the subtree lost one black level),
 *           and rb_fix_left / rb_fix_right repair a UF child exactly as the
 *           Bend fl_* / fr_* helpers do - a red sibling is rotated away
 *           first (fl_red / fr_red), a black sibling with a red child is
 *           rotated and recoloured (fl_b1 / fl_b2c and mirrors), and a black
 *           sibling with two black children is recoloured red so that a red
 *           parent absorbs the missing black and a black one propagates it
 *           (fl_b3 / fr_b3). A deleted internal node is replaced by the
 *           minimum of its right subtree (rb_split_min).
 *   queries find, min, max, lower_bound, the pruned range walk and the
 *           in-order entry walk are the same descents as the Bend source.
 *
 * Nodes are mutated in place and reused: each Bend helper consumes the node it
 * destructures, so reusing that node is exactly what a linear implementation
 * does, and it keeps the reference free of allocator noise.
 */
#ifndef BENCH_REDBLACK_H
#define BENCH_REDBLACK_H

#include "common.h"

typedef struct RB {
  uint8_t red;
  uint32_t k;
  uint64_t v;
  struct RB *l, *r;
} RB;

static RB *rb_pool = NULL;
static RB *rb_freelist = NULL;
static size_t rb_cap = 0, rb_used = 0;

static void rb_init_pool(size_t count) {
  rb_pool = (RB *)malloc(sizeof(RB) * count);
  if (!rb_pool) {
    fprintf(stderr, "red-black node pool allocation failed\n");
    exit(2);
  }
  rb_cap = count;
  rb_used = 0;
  rb_freelist = NULL;
}

static void rb_reset_pool(void) {
  rb_used = 0;
  rb_freelist = NULL;
}

static inline RB *rb_alloc(void) {
  RB *n = rb_freelist;
  if (n) {
    rb_freelist = n->l;
  } else {
    if (rb_used == rb_cap) {
      fprintf(stderr, "red-black node pool exhausted (%zu)\n", rb_cap);
      exit(2);
    }
    n = &rb_pool[rb_used++];
  }
  n->l = n->r = NULL;
  return n;
}

static inline void rb_release(RB *n) {
  n->l = rb_freelist;
  rb_freelist = n;
}

/* ---- insertion (Okasaki) ---- */

/* Repair the one red-red edge a recursive insertion may have created just
 * below the black node t. A red t is returned unchanged: its parent deals
 * with the edge. */
static RB *rb_balance(RB *t) {
  if (t->red) return t;
  RB *l = t->l, *r = t->r;
  if (l && l->red) {
    RB *a = l->l;
    if (a && a->red) { /* bal_ll: rotate right */
      t->l = l->r;
      l->r = t;
      a->red = 0;
      t->red = 0;
      l->red = 1;
      return l;
    }
    RB *m = l->r;
    if (m && m->red) { /* bal_lr: rotate left then right */
      l->r = m->l;
      t->l = m->r;
      m->l = l;
      m->r = t;
      l->red = 0;
      t->red = 0;
      m->red = 1;
      return m;
    }
  }
  if (r && r->red) {
    RB *m = r->l;
    if (m && m->red) { /* bal_rl: rotate right then left */
      r->l = m->r;
      t->r = m->l;
      m->l = t;
      m->r = r;
      r->red = 0;
      t->red = 0;
      m->red = 1;
      return m;
    }
    RB *d = r->r;
    if (d && d->red) { /* bal_rr: rotate left */
      t->r = r->l;
      r->l = t;
      d->red = 0;
      t->red = 0;
      r->red = 1;
      return r;
    }
  }
  return t;
}

static RB *rb_ins(RB *t, uint32_t k, uint64_t v) {
  if (!t) {
    RB *n = rb_alloc();
    n->red = 1;
    n->k = k;
    n->v = v;
    return n;
  }
  if (k < t->k) {
    t->l = rb_ins(t->l, k, v);
    return rb_balance(t);
  }
  if (k > t->k) {
    t->r = rb_ins(t->r, k, v);
    return rb_balance(t);
  }
  t->v = v;
  return t;
}

static RB *rb_insert(RB *t, uint32_t k, uint64_t v) {
  RB *o = rb_ins(t, k, v);
  o->red = 0;
  return o;
}

/* Insert reporting whether the key was NEW, in the SAME descent: the Bend
 * `OrdMap` keeps its entry count inside the insert walk, so a reference that
 * searched first and inserted afterwards would walk the tree twice for the
 * same result and would not be the optimized implementation of this
 * algorithm. */
static RB *rb_ins_n(RB *t, uint32_t k, uint64_t v, int *fresh) {
  if (!t) {
    RB *n = rb_alloc();
    n->red = 1;
    n->k = k;
    n->v = v;
    *fresh = 1;
    return n;
  }
  if (k < t->k) {
    t->l = rb_ins_n(t->l, k, v, fresh);
    return rb_balance(t);
  }
  if (k > t->k) {
    t->r = rb_ins_n(t->r, k, v, fresh);
    return rb_balance(t);
  }
  t->v = v;
  return t;
}

static RB *rb_insert_n(RB *t, uint32_t k, uint64_t v, int *fresh) {
  *fresh = 0;
  RB *o = rb_ins_n(t, k, v, fresh);
  o->red = 0;
  return o;
}

/* ---- deletion ---- */

typedef struct {
  int uf; /* 1: the subtree lost one black level */
  RB *t;
} RBDel;

static inline RBDel rb_td(RB *t) { RBDel d; d.uf = 0; d.t = t; return d; }
static inline RBDel rb_uf(RB *t) { RBDel d; d.uf = 1; d.t = t; return d; }

/* p->l is deficient and p->r is a black sibling (fl_b1 / fl_b2c / fl_b3) */
static RBDel rb_fix_left_black(RB *p) {
  RB *s = p->r;
  int pred = p->red;
  RB *sr = s->r;
  if (sr && sr->red) { /* fl_b1: the sibling's right child is red */
    p->r = s->l;
    p->red = 0;
    s->l = p;
    s->red = (uint8_t)pred;
    sr->red = 0;
    return rb_td(s);
  }
  RB *m = s->l;
  if (m && m->red) { /* fl_b2c: the sibling's left child is red */
    p->r = m->l;
    p->red = 0;
    s->l = m->r;
    s->red = 0;
    m->l = p;
    m->r = s;
    m->red = (uint8_t)pred;
    return rb_td(m);
  }
  /* fl_b3: a black sibling with two black children becomes red */
  s->red = 1;
  p->red = 0;
  return pred ? rb_td(p) : rb_uf(p);
}

/* the left child of p came back as u (p->r is the sibling) */
static RBDel rb_fix_left(RB *p, RBDel u) {
  if (!u.uf) {
    p->l = u.t;
    return rb_td(p);
  }
  RB *s = p->r;
  if (!s) { /* unreachable: a deficient child forces a non-empty sibling */
    p->l = u.t;
    return rb_uf(p);
  }
  if (s->red) { /* fl_red: rotate left, then fix under the now-red parent */
    p->l = u.t;
    p->r = s->l;
    p->red = 1;
    RBDel in = rb_fix_left_black(p);
    s->red = 0;
    s->l = in.t;
    return rb_td(s);
  }
  p->l = u.t;
  return rb_fix_left_black(p);
}

/* p->r is deficient and p->l is a black sibling (fr_b1 / fr_b2c / fr_b3) */
static RBDel rb_fix_right_black(RB *p) {
  RB *s = p->l;
  int pred = p->red;
  RB *sl = s->l;
  if (sl && sl->red) { /* fr_b1: the sibling's left child is red */
    p->l = s->r;
    p->red = 0;
    s->r = p;
    s->red = (uint8_t)pred;
    sl->red = 0;
    return rb_td(s);
  }
  RB *m = s->r;
  if (m && m->red) { /* fr_b2c: the sibling's right child is red */
    p->l = m->r;
    p->red = 0;
    s->r = m->l;
    s->red = 0;
    m->l = s;
    m->r = p;
    m->red = (uint8_t)pred;
    return rb_td(m);
  }
  /* fr_b3 */
  s->red = 1;
  p->red = 0;
  return pred ? rb_td(p) : rb_uf(p);
}

static RBDel rb_fix_right(RB *p, RBDel u) {
  if (!u.uf) {
    p->r = u.t;
    return rb_td(p);
  }
  RB *s = p->l;
  if (!s) {
    p->r = u.t;
    return rb_uf(p);
  }
  if (s->red) { /* fr_red */
    p->r = u.t;
    p->l = s->r;
    p->red = 1;
    RBDel in = rb_fix_right_black(p);
    s->red = 0;
    s->r = in.t;
    return rb_td(s);
  }
  p->r = u.t;
  return rb_fix_right_black(p);
}

/* the smallest entry of t, and what is left of t */
static RBDel rb_split_min(RB *t, uint32_t *mk, uint64_t *mv) {
  if (!t->l) {
    *mk = t->k;
    *mv = t->v;
    RB *r = t->r;
    int red = t->red;
    rb_release(t);
    if (!r) return red ? rb_td(NULL) : rb_uf(NULL);
    r->red = 0; /* blacken: r was red, so the black height is preserved */
    return rb_td(r);
  }
  RBDel u = rb_split_min(t->l, mk, mv);
  return rb_fix_left(t, u);
}

/* delete the entry stored at t itself */
static RBDel rb_del_here(RB *t) {
  if (!t->r) {
    RB *l = t->l;
    int red = t->red;
    rb_release(t);
    if (!l) return red ? rb_td(NULL) : rb_uf(NULL);
    l->red = 0;
    return rb_td(l);
  }
  uint32_t mk;
  uint64_t mv;
  RBDel u = rb_split_min(t->r, &mk, &mv);
  t->k = mk;
  t->v = mv;
  return rb_fix_right(t, u);
}

static RBDel rb_del(RB *t, uint32_t k) {
  if (!t) return rb_td(NULL);
  if (k < t->k) return rb_fix_left(t, rb_del(t->l, k));
  if (k > t->k) return rb_fix_right(t, rb_del(t->r, k));
  return rb_del_here(t);
}

static RB *rb_remove(RB *t, uint32_t k) {
  RB *o = rb_del(t, k).t;
  if (o) o->red = 0;
  return o;
}

/* Delete reporting whether the key was there and what it mapped to, in the
 * SAME descent (the Bend `OrdMap.remove` returns the old value and updates
 * the count inside its own single walk). */
static RBDel rb_del_v(RB *t, uint32_t k, uint64_t *old, int *found) {
  if (!t) return rb_td(NULL);
  if (k < t->k) return rb_fix_left(t, rb_del_v(t->l, k, old, found));
  if (k > t->k) return rb_fix_right(t, rb_del_v(t->r, k, old, found));
  *old = t->v;
  *found = 1;
  return rb_del_here(t);
}

static RB *rb_remove_v(RB *t, uint32_t k, uint64_t *old, int *found) {
  *found = 0;
  RB *o = rb_del_v(t, k, old, found).t;
  if (o) o->red = 0;
  return o;
}

/* ---- queries ---- */

static int rb_find(const RB *t, uint32_t k, uint64_t *out) {
  while (t) {
    if (k < t->k) {
      t = t->l;
    } else if (k > t->k) {
      t = t->r;
    } else {
      *out = t->v;
      return 1;
    }
  }
  return 0;
}

static int rb_min(const RB *t, uint32_t *k, uint64_t *v) {
  if (!t) return 0;
  while (t->l) t = t->l;
  *k = t->k;
  *v = t->v;
  return 1;
}

static int rb_max(const RB *t, uint32_t *k, uint64_t *v) {
  if (!t) return 0;
  while (t->r) t = t->r;
  *k = t->k;
  *v = t->v;
  return 1;
}

/* the first entry with key >= k */
static int rb_lower(const RB *t, uint32_t k, uint32_t *ok, uint64_t *ov) {
  const RB *best = NULL;
  while (t) {
    if (t->k < k) {
      t = t->r;
    } else if (t->k == k) {
      *ok = t->k;
      *ov = t->v;
      return 1;
    } else {
      best = t;
      t = t->l;
    }
  }
  if (!best) return 0;
  *ok = best->k;
  *ov = best->v;
  return 1;
}

/* pruned range walk: fold lo <= key < hi in key order */
static uint32_t rb_range(const RB *t, uint32_t lo, uint32_t hi, uint32_t c, int go) {
  if (!go || !t) return c;
  c = rb_range(t->l, lo, hi, c, lo < t->k);
  if (lo <= t->k && t->k < hi) c = mix(mix(c, t->k), (uint32_t)t->v);
  return rb_range(t->r, lo, hi, c, t->k < hi);
}

static uint32_t rb_entries(const RB *t, uint32_t c) {
  if (!t) return c;
  c = rb_entries(t->l, c);
  c = mix(mix(c, t->k), (uint32_t)t->v);
  return rb_entries(t->r, c);
}

static uint32_t rb_count(const RB *t) {
  if (!t) return 0;
  return 1u + rb_count(t->l) + rb_count(t->r);
}

#endif
