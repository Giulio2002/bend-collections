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

/* Force the compiler to actually perform the measured operation `count`
 * times. Without this, a query whose result is loop-invariant (min, max,
 * length, to_list, new, ...) is hoisted out of the measured loop: region A
 * minus region B then compares `count` Bend operations against ONE C
 * operation, which is not a comparison at all (it shows up as a zero or
 * negative difference). `keep` is the standard DoNotOptimize barrier: an
 * empty asm that launders the state pointer and clobbers memory, so every
 * iteration must re-read the structure and redo the work. It costs the
 * reference the spill/reload of the state fields once per iteration; that is
 * a cost the reference pays, so it is reported as part of the reference
 * time. */
#if defined(__GNUC__) || defined(__clang__)
#define keep(p) __asm__ volatile("" : "+r"(p) : : "memory")
#else
#define keep(p) ((void)0)
#endif

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
  uint32_t order;
} bench_args;

static bench_args parse_args(int argc, char **argv) {
  bench_args a = {0, 0, 0, 0, 0, 0};
  if (argc > 1) a.op = (uint32_t)strtoul(argv[1], NULL, 10);
  if (argc > 2) a.size = (uint32_t)strtoul(argv[2], NULL, 10);
  if (argc > 3) a.count = (uint32_t)strtoul(argv[3], NULL, 10);
  if (argc > 4) a.reps = (uint32_t)strtoul(argv[4], NULL, 10);
  if (argc > 5) a.seed = (uint32_t)strtoul(argv[5], NULL, 10);
  if (argc > 6) a.order = (uint32_t)strtoul(argv[6], NULL, 10);
  return a;
}

static void emit(uint32_t a, uint32_t b, uint32_t c,
                 uint64_t ta, uint64_t tb, uint64_t tc) {
  fprintf(stderr, "%u\n%u\n%u\n", a, b, c);
  printf("TA=%llu TB=%llu TC=%llu\n", (unsigned long long)ta,
         (unsigned long long)tb, (unsigned long long)tc);
}

/* Region driver: `round_fn(op, size, count, nulls, seed)` performs one round
 * -- build a structure of `size`, settle it, run `count` measured operations
 * followed by `nulls` value-stream steps, then destroy it -- and returns its
 * checksum.
 *
 * Three timed regions run that same round with the SAME total number of loop
 * iterations (2k) and the same build and destruction:
 *
 *   A = reps x round(2k measured operations)
 *   B = reps x round( k measured operations)
 *   C = reps x round( 0 measured operations)   the build-and-destroy control
 *
 * so A - B is exactly k x reps measured operations: the build, the settle and
 * the destruction cancel. Because BOTH A and B end in a state the measured
 * operation has been applied to, a size-changing operation no longer moves
 * deallocation work out of the difference -- that is the two-region A/B
 * asymmetry this replaces, which drove A - B negative at large sizes. C is
 * reported next to every row: it is what one region costs with no measured
 * operation at all. The `nulls` parameter of round_fn (value-stream steps
 * that touch no structure) is kept for drivers that need a same-shaped
 * filler; the three regions above do not use it, because the filler measured
 * MORE than some of the operations it would have been subtracted from.
 */
#define BENCH_REGIONS(round_fn)                                               \
  uint32_t acc_a = 0, acc_b = 0, acc_c = 0;                                   \
  uint64_t ta = 0, tb = 0, tc = 0, t0, t1;                                    \
  for (int step = 0; step < 3; step++) {                                      \
    int which = a.order ? 2 - step : step;                                    \
    t0 = now_ns();                                                            \
    if (which == 0)                                                           \
      for (uint32_t p = a.reps; p-- > 0;)                                     \
        acc_a = mix(acc_a, round_fn(a.op, a.size, 2u * a.count, 0u,           \
                                    a.seed + p));                             \
    else if (which == 1)                                                      \
      for (uint32_t p = a.reps; p-- > 0;)                                     \
        acc_b = mix(acc_b, round_fn(a.op, a.size, a.count, 0u,                \
                                    a.seed + p));                             \
    else                                                                      \
      for (uint32_t p = a.reps; p-- > 0;)                                     \
        acc_c = mix(acc_c, round_fn(a.op, a.size, 0u, 0u,                     \
                                    a.seed + p));                             \
    t1 = now_ns();                                                            \
    if (which == 0) ta = t1 - t0;                                             \
    else if (which == 1) tb = t1 - t0;                                        \
    else tc = t1 - t0;                                                        \
  }                                                                           \
  emit(acc_a, acc_b, acc_c, ta, tb, tc);

#define BENCH_MAIN(round_fn, arena_bytes)                                     \
  int main(int argc, char **argv) {                                           \
    bench_args a = parse_args(argc, argv);                                    \
    arena_init(arena_bytes);                                                  \
    BENCH_REGIONS(round_fn)                                                   \
    return 0;                                                                 \
  }

#endif
