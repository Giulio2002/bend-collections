/* C twin of benchmarks/micro.bend: the cost of the four primitives the data
 * structures are built from, measured the same way on both sides.
 *
 *   arith  one LCG step and an add                      (pure uint32 arithmetic)
 *   array  one indexed read + one indexed write of a 4096-slot array
 *   list   one step of a singly-linked-list traversal   (4096-node lists)
 *   alloc  one node of a freshly built + consumed binary tree (8191 nodes)
 *   fresh  one node of a freshly built + consumed 4096-node list
 *
 * `alloc` mallocs and frees every node, which is what a straightforward C
 * implementation of a linked structure does; an arena would be faster still.
 * The numbers are printed in the same "name_ms=" form the Bend program uses,
 * so tools/costmodel.py can pair them up.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#if defined(__GNUC__) || defined(__clang__)
#define keep(p) __asm__ volatile("" : "+r"(p) : : "memory")
#else
#define keep(p) ((void)0)
#endif

static inline uint32_t lcg(uint32_t s) { return s * 1664525u + 1013904223u; }

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

#define ARITH_N 20000000u
#define ARRAY_N 20000000u
#define LIST_LEN 4096u
#define LIST_ROUNDS 5000u
#define TREE_DEPTH 12
#define TREE_ROUNDS 5000u

typedef struct Cell { uint32_t v; struct Cell *next; } Cell;
typedef struct Tr { uint32_t v; struct Tr *l, *r; } Tr;

static Tr *mktree(int d, uint32_t v) {
  Tr *t = (Tr *)malloc(sizeof(Tr));
  if (!t) exit(2);
  if (d == 0) { t->v = v; t->l = t->r = NULL; return t; }
  t->v = 0;
  t->l = mktree(d - 1, v);
  t->r = mktree(d - 1, v + 1u);
  return t;
}

static uint32_t sumtree(Tr *t, uint32_t acc) {
  if (!t->l) { uint32_t v = t->v; free(t); return acc + v; }
  uint32_t a = sumtree(t->l, acc);
  uint32_t b = sumtree(t->r, a);
  free(t);
  return b;
}

int main(void) {
  double t0, t1;
  uint32_t acc, s;

  /* arith */
  t0 = now_ms();
  acc = 0; s = 7;
  for (uint32_t i = 0; i < ARITH_N; i++) { s = lcg(s); acc += s; keep(acc); }
  t1 = now_ms();
  double d1 = t1 - t0;
  fprintf(stderr, "%u\n", acc);

  /* array */
  uint32_t *arr = (uint32_t *)calloc(4096, sizeof(uint32_t));
  if (!arr) return 2;
  t0 = now_ms();
  acc = 0; s = 7;
  for (uint32_t i = 0; i < ARRAY_N; i++) {
    s = lcg(s);
    uint32_t j = s % 4096u;
    uint32_t v = arr[j];
    arr[j] = v + 1u;
    acc += v;
    keep(acc);
  }
  t1 = now_ms();
  double d2 = t1 - t0;
  fprintf(stderr, "%u\n", acc + arr[3]);
  free(arr);

  /* list */
  Cell *head = NULL;
  for (uint32_t i = 0; i < LIST_LEN; i++) {
    Cell *c = (Cell *)malloc(sizeof(Cell));
    if (!c) return 2;
    c->v = 3; c->next = head; head = c;
  }
  t0 = now_ms();
  acc = 0;
  for (uint32_t r = 0; r < LIST_ROUNDS; r++) {
    for (Cell *c = head; c; c = c->next) { acc += c->v; }
    keep(acc);
  }
  t1 = now_ms();
  double d3 = t1 - t0;
  fprintf(stderr, "%u\n", acc);
  while (head) { Cell *n = head->next; free(head); head = n; }

  /* alloc */
  t0 = now_ms();
  acc = 1;
  for (uint32_t r = 0; r < TREE_ROUNDS; r++) {
    acc = sumtree(mktree(TREE_DEPTH, acc), acc);
    keep(acc);
  }
  t1 = now_ms();
  double d4 = t1 - t0;
  fprintf(stderr, "%u\n", acc);

  /* fresh: build and consume a list of the same length every round */
  t0 = now_ms();
  acc = 0;
  for (uint32_t r = 0; r < LIST_ROUNDS; r++) {
    Cell *h = NULL;
    for (uint32_t i = 0; i < LIST_LEN; i++) {
      Cell *c = (Cell *)malloc(sizeof(Cell));
      if (!c) return 2;
      c->v = 3; c->next = h; h = c;
    }
    for (Cell *c = h; c; c = c->next) { acc += c->v; }
    while (h) { Cell *n = h->next; free(h); h = n; }
    keep(acc);
  }
  t1 = now_ms();
  double d5 = t1 - t0;
  fprintf(stderr, "%u\n", acc);

  printf("arith_ms=%.3f array_ms=%.3f list_ms=%.3f alloc_ms=%.3f fresh_ms=%.3f\n",
         d1, d2, d3, d4, d5);
  return 0;
}
