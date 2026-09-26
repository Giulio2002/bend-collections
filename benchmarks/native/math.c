// C reference for src/math/natural.bend (benchmarks/bend/math.bend): the
// same MINSTD argument stream, the same checksum, idiomatic C for each
// function (Euclid with %, sqrt with an integer correction, clz for
// bit_length, left-to-right loops for factorial / perm / comb, binary
// exponentiation, extended Euclid). Prints BENCH_MS=<ms> and the checksum.
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t u64;
#define P31 2147483647ULL

static inline u64 next(u64 r) { return (r * 48271ULL) % P31; }
static inline u64 fold(u64 c, u64 v) { return (c * 31ULL + v % P31) % P31; }

static u64 gcd(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }
static u64 lcm(u64 a, u64 b) { return (a && b) ? a / gcd(a, b) * b : 0; }
static u64 isqrt(u64 n) {
  u64 r = (u64)sqrt((double)n);
  while (r * r > n) r--;
  while ((r + 1) * (r + 1) <= n) r++;
  return r;
}
static u64 ipow(u64 r, int k) { u64 p = 1; while (k--) p *= r; return p; }
static u64 iroot(u64 n, int k) {
  u64 r = (u64)pow((double)n, 1.0 / k);
  while (r && ipow(r, k) > n) r--;
  while (ipow(r + 1, k) <= n) r++;
  return r;
}
static u64 ilog(u64 n, u64 b) { u64 k = 0; while (n >= b) { n /= b; k++; } return k; }
static u64 bit_length(u64 n) { return n ? 64 - __builtin_clzll(n) : 0; }
static u64 factorial(u64 n) { u64 r = 1; for (u64 i = 2; i <= n; i++) r *= i; return r; }
static u64 perm(u64 n, u64 k) { if (k > n) return 0; u64 r = 1; for (u64 i = 0; i < k; i++) r *= n - i; return r; }
static u64 comb(u64 n, u64 k) {
  if (k > n) return 0;
  if (k > n - k) k = n - k;
  u64 r = 1;
  for (u64 i = 0; i < k; i++) r = r * (n - i) / (i + 1);
  return r;
}
static u64 pow_mod(u64 b, u64 e, u64 m) {
  u64 acc = 1 % m; b %= m;
  while (e) { if (e & 1) acc = acc * b % m; b = b * b % m; e >>= 1; }
  return acc;
}
static u64 mod_inverse(u64 a, u64 m) {
  int64_t r0 = (int64_t)m, r1 = (int64_t)(a % m), s0 = 0, s1 = 1;
  while (r1) { int64_t q = r0 / r1, t = r0 - q * r1; r0 = r1; r1 = t; t = s0 - q * s1; s0 = s1; s1 = t; }
  if (r0 != 1) return 0;
  return (u64)(((s0 % (int64_t)m) + (int64_t)m) % (int64_t)m);
}

static u64 step(int op, u64 x, u64 y) {
  switch (op) {
    case 0: return x + y;
    case 1: return gcd(x, y);
    case 2: return lcm(x % 1048576, y % 1048576);
    case 3: return isqrt(x);
    case 4: return iroot(x, 3);
    case 5: return ilog(1 + x, 10);
    case 6: return bit_length(x);
    case 7: return factorial(x % 13);
    case 8: return perm(x % 16, y % 17);
    case 9: return comb(x % 41, y % 42);
    case 10: return pow_mod(x % 1048576, y % 1048576, 1 + (x + y) % 16777215);
    case 11: return mod_inverse(x % 16777216, 16777213);
    case 12: { u64 d = 1 + y % 1048576; return x / d + x % d; }
  }
  return 0;
}

static const char *NAMES[] = {"loop", "gcd", "lcm", "isqrt", "iroot3", "ilog10", "bit_length", "factorial", "perm", "comb", "pow_mod", "mod_inverse", "divmod"};

int main(void) {
  const char *name = getenv("MATH_OP"), *cs = getenv("MATH_COUNT");
  int op = -1;
  for (int i = 0; i < 13; i++) if (name && !strcmp(name, NAMES[i])) op = i;
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
