// C reference for the templated math per type (benchmarks/bend/typed.bend):
// the same MINSTD arguments and checksum, idiomatic uint32_t / uint64_t /
// float / double code with the same checked semantics (a result that does
// not fit counts as 0): Euclid with %, sqrt with an integer correction,
// comb and factorial in a wider type with an overflow test, binary
// exponentiation (a 128-bit product for u64 mod m), and float/double powers
// by the same square-and-multiply order. Prints BENCH_MS=<ms> and the sum.
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;
#define P31 2147483647ULL

static inline u64 next(u64 r) { return (r * 48271ULL) % P31; }
static inline u64 fold(u64 c, u64 v) { return (c * 31ULL + v % P31) % P31; }

static u64 gcd64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }
static u64 isqrt64(u64 n) {
  u64 r = (u64)sqrtl((long double)n);
  while (r > 0 && (u128)r * r > n) r--;
  while ((u128)(r + 1) * (r + 1) <= n) r++;
  return r;
}
// C(n, k) if it fits below 2^w, else 0
static u64 comb_w(u64 n, u64 k, int w) {
  if (k > n) return 0;
  if (k > n - k) k = n - k;
  u128 r = 1, lim = (u128)1 << w;
  for (u64 i = 0; i < k; i++) {
    r = r * (n - i) / (i + 1);
    if (r >= lim) return 0;
  }
  return (u64)r;
}
static u64 fact_w(u64 n, int w) {
  u128 r = 1, lim = (u128)1 << w;
  for (u64 i = 2; i <= n; i++) { r *= i; if (r >= lim) return 0; }
  return (u64)r;
}
static u64 pow_mod64(u64 b, u64 e, u64 m) {
  u64 acc = 1 % m; b %= m;
  while (e) { if (e & 1) acc = (u64)((u128)acc * b % m); e >>= 1; if (e) b = (u64)((u128)b * b % m); }
  return acc;
}
static u32 pow_mod32(u32 b, u32 e, u32 m) {
  u64 acc = 1 % m, bb = b % m;
  while (e) { if (e & 1) acc = acc * bb % m; e >>= 1; if (e) bb = bb * bb % m; }
  return (u32)acc;
}
static float powf_sm(float x, unsigned k) {
  float acc = 1.0f, base = x;
  while (k) { if (k & 1) acc = acc * base; if (k > 1) base = base * base; k >>= 1; }
  return acc;
}
static double pow_sm(double x, unsigned k) {
  double acc = 1.0, base = x;
  while (k) { if (k & 1) acc = acc * base; if (k > 1) base = base * base; k >>= 1; }
  return acc;
}
static u64 fbits(float f) { u32 b; memcpy(&b, &f, 4); return b; }
static u64 dbits(double d) { u64 b; memcpy(&b, &d, 8); return b; }
static double dfrom(u64 hi, u64 lo) { u64 b = (hi << 32) | lo; double d; memcpy(&d, &b, 8); return d; }
static float fv(u64 x) { return (float)(x % 1000) / 7.0f; }
static double da(u64 x, u64 y) { return dfrom(1072693248ULL + x % 1048576, y); }
static double db(u64 x, u64 y) { return dfrom(1073741824ULL + y % 1048576, x); }
static float clampf_py(float x, float lo, float hi) {
  if (hi < lo) return 0.0f;
  float m = lo > x ? lo : x;      // max(x, lo): x unless x < lo
  return hi < m ? hi : m;         // min(m, hi): m unless hi < m
}

static u64 step(int op, u64 x, u64 y) {
  switch (op) {
    case 0: return gcd64((u32)x, (u32)y);
    case 1: return isqrt64((u32)(x * 2 + y % 2));
    case 2: return comb_w(x % 41, y % 42, 32);
    case 3: return fact_w(x % 14, 32);
    case 4: return pow_mod32((u32)x, (u32)y, (u32)(1 + (x + y) % 4294967295ULL));
    case 5: return gcd64((x << 32) | y, (y << 32) | x);
    case 6: return isqrt64(((x * 2) << 32) | y);
    case 7: return comb_w(x % 68, y % 69, 64);
    case 8: return fact_w(x % 22, 64);
    case 9: return pow_mod64((x << 32) | y, y, (y << 32) | (x / 2 * 2 + 1));
    case 10: return fbits(powf_sm(fv(x), (unsigned)(y % 16)));
    case 11: return fbits(clampf_py(fv(x), fv(y), fv(y) + 50.0f));
    case 12: return dbits(da(x, y) + db(x, y));
    case 13: return dbits(da(x, y) * db(x, y));
    case 14: return dbits(da(x, y) / db(x, y));
    case 15: return dbits(sqrt(db(x, y)));
    case 16: return dbits(pow_sm(da(x, y), (unsigned)(y % 16)));
    case 17: return dbits(da(x, y));
  }
  return 0;
}

static const char *NAMES[] = {"u32_gcd", "u32_isqrt", "u32_comb", "u32_factorial", "u32_pow_mod", "u64_gcd",
  "u64_isqrt", "u64_comb", "u64_factorial", "u64_pow_mod", "f32_pow", "f32_clamp", "f64_add", "f64_mul",
  "f64_div", "f64_sqrt", "f64_pow", "loop"};

int main(void) {
  const char *name = getenv("TYPED_OP"), *cs = getenv("TYPED_COUNT");
  int op = -1;
  for (int i = 0; i < 18; i++) if (name && !strcmp(name, NAMES[i])) op = i;
  u64 count = cs ? strtoull(cs, 0, 10) : 0, r = 12345, c = 0;
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  for (u64 i = 0; i < count; i++) {
    u64 x = next(r), y = next(x);
    c = fold(c, step(op, x, y));
    r = y;
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;
  printf("BENCH_MS=%.3f\n%llu\n", ms, (unsigned long long)c);
  return 0;
}
