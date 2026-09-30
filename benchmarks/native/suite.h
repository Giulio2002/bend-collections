/* Shared scaffolding of the C references of benchmarks/crypto_suite.py; the
   Bend side is benchmarks/bend/suite.bend. BENCH_INPUT names a file cut into
   messages of BENCH_SIZE bytes before the timed region; BENCH_PARAM selects a
   variant; after the timed region BENCH_MS and SUM (every output byte folded
   as c = c * 31 + byte, last message first) are printed. */
#ifndef SUITE_H
#define SUITE_H
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static size_t env_num(const char *name, size_t dflt) {
  const char *s = getenv(name);
  return s ? (size_t)strtoull(s, 0, 10) : dflt;
}

typedef struct { uint8_t *data; size_t size, count; } messages;

static messages load_messages(void) {
  messages m = {0, env_num("BENCH_SIZE", 0), 0};
  const char *path = getenv("BENCH_INPUT");
  FILE *f = path ? fopen(path, "rb") : 0;
  if (!f || !m.size) { fprintf(stderr, "BENCH_INPUT/BENCH_SIZE\n"); exit(1); }
  fseek(f, 0, SEEK_END); size_t n = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  m.data = malloc(n ? n : 1);
  if (fread(m.data, 1, n, f) != n) exit(1);
  fclose(f);
  m.count = n / m.size;
  return m;
}

static const uint8_t *msg(const messages *m, size_t i) { return m->data + i * m->size; }

/* n bytes (a * i + b) mod 256 */
static void pattern(uint8_t *out, size_t n, uint32_t a, uint32_t b) {
  for (size_t i = 0; i < n; i++) out[i] = (uint8_t)(a * (uint32_t)i + b);
}

static uint32_t fold(uint32_t c, const uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) c = c * 31 + p[i];
  return c;
}

/* outputs of equal length, stored in message order */
static uint32_t fold_outputs(const uint8_t *out, size_t count, size_t len) {
  uint32_t c = 0;
  for (size_t i = count; i-- > 0;) c = fold(c, out + i * len, len);
  return c;
}

static double now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec * 1e-6;
}

static void report(double ms, uint32_t sum) {
  printf("BENCH_MS=%.4f\nSUM=%u\n", ms, sum);
}
#endif
