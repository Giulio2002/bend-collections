#ifndef DLIST_ARENA_H
#define DLIST_ARENA_H
#include "common.h"
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


#endif
