/* Shared scaffolding for the optimized C reference implementations.
 *
 * Every reference program takes the same argv as its Bend counterpart in
 * benchmarks/bend/, draws its arguments from the identical LCG, folds results
 * with the identical mix(), and prints
 *     stderr: <checksum A>\n<checksum B>\n
 *     stdout: TA=<ns> TB=<ns>\n
 * so benchmarks/run.py can compare both the answers and the timings.
 * (The Bend driver prints milliseconds; run.py converts.)
 *
 * Region A = reps x (build a structure of `size`, then `count` measured ops)
 * Region B = reps x (build a structure of `size`, then `count` value-stream
 *                    steps), so A - B isolates the measured operations.
 *
 * Memory: a bump arena reset once per round. This is the normal efficient
 * choice for a short-lived C benchmark; nothing here is slowed down on
 * purpose.
 */
#ifndef BENCH_COMMON_H
#define BENCH_COMMON_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static inline uint32_t lcg(uint32_t s) { return s * 1664525u + 1013904223u; }
static inline uint32_t mix(uint32_t c, uint32_t v) { return c * 31u + v; }

static inline uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

/* ---- bump arena ---- */

static unsigned char *arena_base = NULL;
static size_t arena_cap = 0, arena_off = 0;

static void arena_init(size_t bytes) {
  arena_base = (unsigned char *)malloc(bytes);
  if (!arena_base) {
    fprintf(stderr, "arena allocation of %zu bytes failed\n", bytes);
    exit(2);
  }
  arena_cap = bytes;
  arena_off = 0;
}

static inline void *arena_alloc(size_t bytes) {
  size_t off = (arena_off + 15u) & ~(size_t)15u;
  if (off + bytes > arena_cap) {
    fprintf(stderr, "arena exhausted (%zu of %zu)\n", off + bytes, arena_cap);
    exit(2);
  }
  arena_off = off + bytes;
  return arena_base + off;
}

static inline void arena_reset(void) { arena_off = 0; }

/* ---- argv ---- */

typedef struct {
  uint32_t op;
  uint32_t size;
  uint32_t count;
  uint32_t reps;
  uint32_t seed;
} bench_args;

static bench_args parse_args(int argc, char **argv) {
  bench_args a = {0, 0, 0, 0, 0};
  if (argc > 1) a.op = (uint32_t)strtoul(argv[1], NULL, 10);
  if (argc > 2) a.size = (uint32_t)strtoul(argv[2], NULL, 10);
  if (argc > 3) a.count = (uint32_t)strtoul(argv[3], NULL, 10);
  if (argc > 4) a.reps = (uint32_t)strtoul(argv[4], NULL, 10);
  if (argc > 5) a.seed = (uint32_t)strtoul(argv[5], NULL, 10);
  return a;
}

static void emit(uint32_t a, uint32_t b, uint64_t ta, uint64_t tb) {
  fprintf(stderr, "%u\n%u\n", a, b);
  printf("TA=%llu TB=%llu\n", (unsigned long long)ta, (unsigned long long)tb);
}

/* Region driver: `round_fn(op, size, count, seed)` performs one round and
 * returns its checksum; op == NULL_OP runs the value-stream-only body. */
#define BENCH_MAIN(round_fn, arena_bytes)                                     \
  int main(int argc, char **argv) {                                           \
    bench_args a = parse_args(argc, argv);                                    \
    arena_init(arena_bytes);                                                  \
    uint32_t acc_a = 0, acc_b = 0;                                            \
    uint64_t t0 = now_ns();                                                   \
    for (uint32_t p = a.reps; p-- > 0;)                                       \
      acc_a = mix(acc_a, round_fn(a.op, a.size, a.count, a.seed + p));        \
    uint64_t t1 = now_ns();                                                   \
    uint64_t t2 = now_ns();                                                   \
    for (uint32_t p = a.reps; p-- > 0;)                                       \
      acc_b = mix(acc_b, round_fn(NULL_OP, a.size, a.count, a.seed + p));     \
    uint64_t t3 = now_ns();                                                   \
    emit(acc_a, acc_b, t1 - t0, t3 - t2);                                     \
    return 0;                                                                 \
  }

#endif
