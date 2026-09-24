/* Same fixed fields, LCG, four edits/round and final hash as churn.bend. */
#include <stdint.h>
#include <stdio.h>
#include <time.h>

static uint32_t cells[128];

static void prepend(uint32_t root, uint32_t node) {
  uint32_t head = cells[root];
  cells[32 + node] = head;
  if (head) cells[64 + head] = node;
  cells[root] = node;
}

static void remove_node(uint32_t root, uint32_t node) {
  uint32_t after = cells[32 + node], before = cells[64 + node];
  if (after) cells[64 + after] = before;
  if (before) {
    cells[32 + before] = after;
    cells[64 + node] = 0;
  } else {
    cells[root] = after;
  }
  cells[32 + node] = 0;
}

int main(void) {
  for (uint32_t n = 31; n; --n) prepend(0, n);
  uint32_t rng = 1;
  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);
  for (unsigned i = 0; i < 100000; ++i) {
    uint32_t n = 1 + rng % 31;
    remove_node(0, n); prepend(1, n);
    remove_node(1, n); prepend(0, n);
    rng = rng * 1664525u + 1013904223u;
  }
  clock_gettime(CLOCK_MONOTONIC, &end);
  uint32_t hash = 0;
  for (unsigned i = 128; i; --i) hash = hash * 33u + cells[i-1];
  unsigned long long ns = (end.tv_sec-start.tv_sec)*1000000000ull + end.tv_nsec-start.tv_nsec;
  printf("%u\n", hash);
  fprintf(stderr, "IL_NS %llu\n", ns);
  return 0;
}
