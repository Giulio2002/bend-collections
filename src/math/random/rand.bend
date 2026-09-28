import Base
import ../u64.bend as W
import ../w64.bend as X
import ../f64.bend as F

# Random values from any source, written once: Go's math/rand/v2 Rand
# methods, bit for bit (the 64-bit code paths).
#
# The Source interface. A source is any state type S with a step
#
#   ~next: S -> W.U64 & S       the next 64-bit output and the new state
#
# passed as templates (~S, ~next), as src/math/num.bend passes a numeric
# type's ~op and ~test: each source compiles to its own copy with next
# inlined, and the state is threaded explicitly (Bend is pure: every
# function returns its value next to the advanced state). The sources here
# are chacha8.bend's ChaCha8 and pcg.bend's PCG:
#
#   import ./src/math/random.bend as R
#   import ./src/math/random/chacha8.bend as C8
#   (k, g) = R.uint64n(~C8.ChaCha8, ~R.chacha8_next, g, n)
#
# A later module (math/statistics: normal, exponential, ...) is written the
# same way, once for every source, on top of these functions:
#
#   def normal(~S: Data, ~next: S -> W.U64 & S, s: S) -> F.F64 & S:
#     ... R.float64(~S, ~next, s) ...
#
# and its laws can be stated and proved for an arbitrary ~next (a template
# proof is checked once, for every source; proofs/math/random/rand.bend).
#
#   uint64(s)            next(s)                           Go Uint64
#   uint32(s)            the top 32 bits                   Go Uint32
#   int64(s)             the low 63 bits                   Go Int64
#   int32(s)             the top 31 bits                   Go Int32
#   uint64n(s, n)        uniform in [0, n) for n > 0       Go Uint64N
#                        (uint_below is the same function; n == 0 is read
#                        as 2^64, Go's internal uint64n(0): a full uint64)
#   uint32n(s, n)        uniform in [0, n), n: U32 > 0      Go Uint32N
#   intn(s, n)           uniform in [0, n), n: Nat,        Go IntN
#                        0 < n < 2^48 (a Nat's run-time bound); 0 for n == 0
#   int_range(s, lo, hi) uniform in [lo, hi), lo < hi     lo + IntN(hi - lo)
#   float64(s)           uniform multiple of 2^-53 in [0, 1)  Go Float64
#   shuffle(s, xs)       a Fisher-Yates permutation of xs  Go Shuffle
#   perm(s, n)           a random permutation of 0..n-1    Go Perm
#
# uint64n is Lemire's nearly divisionless method ("Fast Random Integer
# Generation in an Interval", ACM TOMACS 2019), exactly as Go's uint64n:
# a power of two n masks the low bits; otherwise the 128-bit product x * n
# is split into hi:lo, and x is rejected while lo < 2^64 mod n (computed,
# with a division, only when lo < n). The accepted x map onto every k < n
# equally often (proved: proofs/math/random/lemire.bend), so the output is
# exactly uniform for a uniform source. Go retries forever; here at most
# 128 draws are made (Bend requires termination): a uniform source rejects
# with probability below 1/2 per draw, so the 128th rejection has
# probability below 2^-128, and even then the result is below n.

def fst(-A: Data, -S: Data, p: A & S) -> A:
  (a, s) = p
  a

def snd(-A: Data, -S: Data, p: A & S) -> S:
  (a, s) = p
  s

def uint64(~S: Data, ~next: S -> W.U64 & S, s: S) -> W.U64 & S:
  next(s)

def top32(-S: Data, p: W.U64 & S) -> U32 & S:
  (x, s) = p
  (X.hi(x), s)

def uint32(~S: Data, ~next: S -> W.U64 & S, s: S) -> U32 & S:
  top32(S, next(s))

def low63(-S: Data, p: W.U64 & S) -> W.U64 & S:
  (+x, s) = p
  (W.U64{X.lo(x), U32.and(X.hi(x), 2147483647)}, s)

def int64(~S: Data, ~next: S -> W.U64 & S, s: S) -> W.U64 & S:
  low63(S, next(s))

def top31(-S: Data, p: W.U64 & S) -> U32 & S:
  (x, s) = p
  (U32.shr(X.hi(x)), s)

def int32(~S: Data, ~next: S -> W.U64 & S, s: S) -> U32 & S:
  top31(S, next(s))

# ---- bounded integers: Lemire ----

def and64(+a: W.U64, +b: W.U64) -> W.U64:
  W.U64{U32.and(X.lo(a), X.lo(b)), U32.and(X.hi(a), X.hi(b))}

# n & (n - 1) == 0: n is a power of two (or zero)
def is_pow2(+n: W.U64) -> Bool:
  X.is_zero(and64(n, X.sub(n, W.U64{1, 0})))

def mask(-S: Data, +n: W.U64, p: W.U64 & S) -> W.U64 & S:
  (+x, s) = p
  (and64(x, X.sub(n, W.U64{1, 0})), s)

# 2^64 mod n = (2^64 - n) mod n, for n > 0 (Go: -n % n)
def thresh(+n: W.U64) -> W.U64:
  X.rem(X.sub(W.U64{0, 0}, n), n)

# the draw x as the product x * n = hi:lo, kept with the state
type Draw<-S: Data> is Data:
  D{hi: W.U64, lo: W.U64, s: S}

def draw_fin(-S: Data, s: S, p: W.U64 & W.U64) -> Draw<S>:
  (lo, hi) = p
  D{hi, lo, s}

def draw(-S: Data, +n: W.U64, p: W.U64 & S) -> Draw<S>:
  (+x, s) = p
  draw_fin(S, s, X.mul128(x, n))

# one rejection step: while lo < t, draw again; an accepted draw is kept
def again(~S: Data, ~next: S -> W.U64 & S, +n: W.U64, +hi: W.U64, +lo: W.U64, s: S, reject: Bool) -> Draw<S>:
  match reject:
    case False{}:
      D{hi, lo, s}
    case True{}:
      draw(S, n, next(s))

def step(~S: Data, ~next: S -> W.U64 & S, +n: W.U64, +t: W.U64, d: Draw<S>) -> Draw<S>:
  match d:
    case D{+hi, +lo, s}:
      again(~S, ~next, n, hi, lo, s, X.lt(lo, t))

# fuel rejection steps (an accepted draw is a fixed point of step)
def retry(~S: Data, ~next: S -> W.U64 & S, fuel: Nat, +n: W.U64, +t: W.U64, d: Draw<S>) -> Draw<S>:
  match fuel:
    case 0n:
      d
    case 1n+f:
      retry(~S, ~next, f, n, t, step(~S, ~next, n, t, d))

def result(-S: Data, d: Draw<S>) -> W.U64 & S:
  match d:
    case D{hi, lo, s}:
      (hi, s)

# lo >= n >= t accepts at once; otherwise t = 2^64 mod n is computed and at
# most 127 more draws are made
def lemire_small(~S: Data, ~next: S -> W.U64 & S, +n: W.U64, +hi: W.U64, +lo: W.U64, s: S, small: Bool) -> W.U64 & S:
  match small:
    case False{}:
      (hi, s)
    case True{}:
      result(S, retry(~S, ~next, 127n, n, thresh(n), D{hi, lo, s}))

def lemire_first(~S: Data, ~next: S -> W.U64 & S, +n: W.U64, d: Draw<S>) -> W.U64 & S:
  match d:
    case D{+hi, +lo, s}:
      lemire_small(~S, ~next, n, hi, lo, s, X.lt(lo, n))

def uint64n_pick(~S: Data, ~next: S -> W.U64 & S, s: S, +n: W.U64, pow2: Bool) -> W.U64 & S:
  match pow2:
    case True{}:
      mask(S, n, next(s))
    case False{}:
      lemire_first(~S, ~next, n, draw(S, n, next(s)))

# uniform in [0, n) for n > 0 (Go's Uint64N)
def uint64n(~S: Data, ~next: S -> W.U64 & S, s: S, +n: W.U64) -> W.U64 & S:
  uint64n_pick(~S, ~next, s, n, is_pow2(n))

def uint_below(~S: Data, ~next: S -> W.U64 & S, s: S, +n: W.U64) -> W.U64 & S:
  uint64n(~S, ~next, s, n)

def lo32(-S: Data, p: W.U64 & S) -> U32 & S:
  (x, s) = p
  (X.lo(x), s)

# uniform in [0, n) for n > 0 (Go's Uint32N)
def uint32n(~S: Data, ~next: S -> W.U64 & S, s: S, +n: U32) -> U32 & S:
  lo32(S, uint64n(~S, ~next, s, W.U64{n, 0}))

def to_nat(-S: Data, p: W.U64 & S) -> Nat & S:
  (x, s) = p
  (X.n48(x), s)

def intn_z(~S: Data, ~next: S -> W.U64 & S, s: S, +n: Nat, z: Bool) -> Nat & S:
  match z:
    case True{}:
      (0n, s)
    case False{}:
      to_nat(S, uint64n(~S, ~next, s, X.of48(n)))

# uniform in [0, n) for 0 < n < 2^48 (Go's IntN); (0, s) for n == 0
def intn(~S: Data, ~next: S -> W.U64 & S, s: S, +n: Nat) -> Nat & S:
  intn_z(~S, ~next, s, n, Nat.is_eq(n, 0n))

def plus(-S: Data, +lo: Nat, p: Nat & S) -> Nat & S:
  (k, s) = p
  (Nat.add(lo, k), s)

# uniform in [lo, hi) for lo < hi, hi - lo < 2^48; (lo, s) when hi <= lo
def int_range(~S: Data, ~next: S -> W.U64 & S, s: S, +lo: Nat, +hi: Nat) -> Nat & S:
  plus(S, lo, intn(~S, ~next, s, Nat.sub(hi, lo)))

# ---- floats ----

# x >> 11 as a double divided by 2^53: for m = x >> 11 > 0 with c leading
# zeros (11 <= c <= 63), m << (c - 11) has its top bit at 52, and the value
# m 2^-53 is that significand with biased exponent 1033 - c (below 1023)
def f53(+m: W.U64, +c: Nat) -> F.F64:
  F.Bits{X.lo(X.shl(m, Nat.sub(c, 11n))), U32.add(U32.mul(U32.from_nat(Nat.sub(1033n, c)), 1048576), U32.and(X.hi(X.shl(m, Nat.sub(c, 11n))), 1048575))}

def f53_z(+m: W.U64, z: Bool) -> F.F64:
  match z:
    case True{}:
      F.zero(False{})
    case False{}:
      f53(m, X.clz(m))

# Go's Float64: float64(x << 11 >> 11) / (1 << 53), the low 53 bits
def to_float(+x: W.U64) -> F.F64:
  f53_z(W.U64{X.lo(x), U32.and(X.hi(x), 2097151)}, X.is_zero(W.U64{X.lo(x), U32.and(X.hi(x), 2097151)}))

def float_of(-S: Data, p: W.U64 & S) -> F.F64 & S:
  (+x, s) = p
  (to_float(x), s)

def float64(~S: Data, ~next: S -> W.U64 & S, s: S) -> F.F64 & S:
  float_of(S, next(s))

# ---- permutations ----

def nth(-A: Data, xs: List<&2, A>, i: Nat) -> Maybe<&2, A>:
  match xs i:
    case Nil{} _:
      None{}
    case Con{h, t} 0n:
      Some{h}
    case Con{h, t} 1n+p:
      nth(A, t, p)

def put(-A: Data, xs: List<&2, A>, i: Nat, x: A) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{x, t}
    case Con{h, t} 1n+p:
      Con{h, put(A, t, p, x)}

def swap_m(-A: Data, xs: List<&2, A>, +i: Nat, +j: Nat, a: Maybe<&2, A>, b: Maybe<&2, A>) -> List<&2, A>:
  match a b:
    case Some{x} Some{y}:
      put(A, put(A, xs, i, y), j, x)
    case _ _:
      xs

# exchange elements i and j (unchanged when either is out of range)
def swap(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat) -> List<&2, A>:
  swap_m(A, xs, i, j, nth(A, xs, i), nth(A, xs, j))

def swap_at(-A: Data, -S: Data, xs: List<&2, A>, +i: Nat, p: W.U64 & S) -> List<&2, A> & S:
  (+j, s) = p
  (swap(A, xs, i, X.n48(j)), s)

# the length as a 64-bit word
def len64(-A: Data, xs: List<&2, A>) -> W.U64:
  match xs:
    case Nil{}:
      W.U64{0, 0}
    case Con{x, rest}:
      X.add(len64(A, rest), W.U64{1, 0})

# swap element i with a uniform j < n = i + 1
def shuffle_step(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +i: Nat, +n: W.U64, st: List<&2, A> & S) -> List<&2, A> & S:
  (xs, s) = st
  swap_at(A, S, xs, i, uint64n(~S, ~next, s, n))

# i = k, k - 1, ..., 1 with the bound n = i + 1 as a 64-bit word
def shuffle_go(~A: Data, ~S: Data, ~next: S -> W.U64 & S, k: Nat, +n: W.U64, st: List<&2, A> & S) -> List<&2, A> & S:
  match k:
    case 0n:
      st
    case 1n+ +p:
      shuffle_go(~A, ~S, ~next, p, X.sub(n, W.U64{1, 0}), shuffle_step(~A, ~S, ~next, 1n+p, n, st))

# Go's Shuffle (Fisher-Yates, from the last index down), for fewer than 2^48
# elements
def shuffle(~A: Data, ~S: Data, ~next: S -> W.U64 & S, s: S, +xs: List<&2, A>) -> List<&2, A> & S:
  shuffle_go(~A, ~S, ~next, Nat.sub(List.length(&2, A, xs), 1n), len64(A, xs), (xs, s))

def range_go(n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+ +p:
      range_go(p, Con{p, acc})

# [0, 1, ..., n - 1]
def range(n: Nat) -> List<&2, Nat>:
  range_go(n, [])

# Go's Perm: a shuffle of 0..n-1
def perm(~S: Data, ~next: S -> W.U64 & S, s: S, +n: Nat) -> List<&2, Nat> & S:
  shuffle(~Nat, ~S, ~next, s, range(n))
