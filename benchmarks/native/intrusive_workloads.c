/* Same application work as intrusive_{transfer,pulses}.bend. Plain indexed
 * C establishes a reference for the preconditioned intrusive representation;
 * it is not a replacement for the checked generational DList comparator. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static uint32_t *cells;
static uint32_t pool, available;
static uint32_t mix(uint32_t h, uint32_t n) { return h * 33u + n; }
static uint32_t lcg(uint32_t n) { return n * 1664525u + 1013904223u; }
static void note(uint32_t n) { cells[3] = mix(cells[3], n); }

static void prepend(uint32_t root, uint32_t n) {
  uint32_t head = cells[root];
  cells[8*n] = head;
  if (head) cells[8*head+1] = n;
  cells[root] = n;
}
static void remove_node(uint32_t root, uint32_t n) {
  uint32_t next = cells[8*n], prev = cells[8*n+1];
  if (next) cells[8*next+1] = prev;
  if (prev) { cells[8*prev] = next; cells[8*n+1] = 0; }
  else cells[root] = next;
  cells[8*n] = 0;
}
static void release(uint32_t n) {
  cells[8*n] = pool; pool = n; available++;
}
static uint32_t take(void) {
  if (!pool) abort(); /* prewarmed capacity is part of the workload */
  uint32_t n = pool;
  pool = cells[8*n]; cells[8*n] = 0; available--;
  return n;
}
static void pulse(uint32_t size, uint32_t seed) {
  for (uint32_t k = size; k; --k) {
    uint32_t n = take();
    cells[8*n+2] = seed; cells[8*k+6] = n;
    prepend(0, n); seed = lcg(seed);
  }
  for (uint32_t k = size; k; --k) {
    uint32_t n = cells[8*k+6];
    note(n); note(cells[8*n+2]);
    remove_node(0, n); release(n);
  }
}
static void observe(uint32_t head, uint32_t size) {
  for (uint32_t k = 0; head && k < size; ++k) {
    note(head); head = cells[8*head];
  }
  if (head) abort();
}

int main(int argc, char **argv) {
  if (argc != 5) return 2;
  uint32_t mode = (uint32_t)strtoul(argv[1], NULL, 10);
  uint32_t size = (uint32_t)strtoul(argv[2], NULL, 10);
  uint32_t count = (uint32_t)strtoul(argv[3], NULL, 10);
  uint32_t seed = (uint32_t)strtoul(argv[4], NULL, 10);
  if (mode > 1 || !size || size > 65536 || !count) return 2;
  cells = calloc(8 * ((size_t)size + 1), sizeof(uint32_t));
  if (!cells) return 3;
  if (mode == 0) {
    for (uint32_t n = size; n; --n) {
      cells[8*n+2] = mix(n, 17); prepend(0, n);
    }
  } else {
    for (uint32_t n = 1; n <= size; ++n) release(n);
    cells[2] = size;
    pulse(size, 0); cells[3] = 0;
  }
  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);
  if (mode == 0) {
    for (uint32_t i = 0; i < count; ++i) {
      uint32_t n = 1 + seed / 256 % size, owner = cells[8*n+5];
      remove_node(owner, n); prepend(1-owner, n); cells[8*n+5] = 1-owner;
      seed = lcg(seed);
    }
  } else {
    for (uint32_t i = 0; i < count; ++i) {
      pulse(size, seed); seed = lcg(seed);
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &end);
  if (mode == 0) {
    note(UINT32_MAX); observe(cells[0], size);
    note(UINT32_MAX); observe(cells[1], size);
  } else {
    note(available); observe(pool, size); note(cells[0]);
  }
  for (uint32_t n = size; n; --n) { note(n); note(cells[8*n+2]); }
  printf("%u %u %u\n", cells[3], cells[2], cells[4]);
  fprintf(stderr, "IL_NS %llu\n", (unsigned long long)
      ((end.tv_sec-start.tv_sec)*1000000000ull + end.tv_nsec-start.tv_nsec));
  free(cells);
  return 0;
}
