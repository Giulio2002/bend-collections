import Base
import ./u64.bend as W
import ./f64.bend as F
import ./random/rand.bend as R
import ./random/chacha8.bend as C8
import ./random/pcg.bend as P

# Pseudorandom numbers, shaped like Go's math/rand/v2: a generator is a value
# built from a seed the caller chooses (the same seed gives the same
# sequence, bit for bit Go's), threaded explicitly: every call returns its
# value next to the advanced generator.
#
#   import ./src/math/random.bend as R
#   import ./src/math/random/pcg.bend as PCG           (the state types:
#   import ./src/math/random/chacha8.bend as C8         PCG.PCG, C8.ChaCha8)
#
#   R.pcg(W.U64{1, 0}, W.U64{2, 0})                   Go: rand.NewPCG(1, 2)
#   R.uint64n(~PCG.PCG, ~R.pcg_next, g, n)            Go: r.Uint64N(n)
#   R.shuffle(~U32, ~PCG.PCG, ~R.pcg_next, g, xs)     Go: r.Shuffle
#
# (each call returns the value next to the advanced generator: a pair, taken
# apart in a helper def, as Bend matches only parameters)
#
# Sources (the Source interface of random/rand.bend: a state type S and
# ~next: S -> W.U64 & S, passed as templates):
#
#   chacha8(seed), chacha8_next   Go's ChaCha8 = C2SP chacha8rand, a 32-byte
#                                 seed (None unless 32 bytes < 256); a CSPRNG
#                                 (for secrets use src/crypto/random.bend)
#   pcg(seed1, seed2), pcg_next   Go's PCG (128-bit LCG, DXSM output); fast,
#                                 not cryptographic
#
# Functions over any source (random/rand.bend has the details):
#
#   uint64 uint32 int64 int32     raw words
#   uint64n / uint_below, uint32n, intn, int_range
#                                 uniform bounded integers (Lemire, unbiased)
#   float64                       uniform in [0, 1), 53 random bits
#   shuffle, perm                 Fisher-Yates on a list (through an array)
#   shuffle_array                 Fisher-Yates in place on the first n slots
#                                 of an Array (Go's Shuffle on a slice)
#
# Laws (spec/math/random/, proved in proofs/math/random/): the ChaCha8
# stream is C2SP's for every seed, one PCG step is the 128-bit LCG and DXSM
# on naturals, uint64n(n) < n, Lemire's acceptance is exactly unbiased
# (every k < n has floor(2^64 / n) accepted inputs), shuffle and perm return
# permutations (shuffle_array: of the array's slots), float64 < 1.

def chacha8(+seed: List<&2, U32>) -> Maybe<&2, C8.ChaCha8>:
  C8.new(seed)

def chacha8_next(g: C8.ChaCha8) -> W.U64 & C8.ChaCha8:
  C8.next(g)

def pcg(+seed1: W.U64, +seed2: W.U64) -> P.PCG:
  P.new(seed1, seed2)

def pcg_next(p: P.PCG) -> W.U64 & P.PCG:
  P.next(p)

def uint64(~S: Data, ~next: S -> W.U64 & S, s: S) -> W.U64 & S:
  R.uint64(~S, ~next, s)

def uint32(~S: Data, ~next: S -> W.U64 & S, s: S) -> U32 & S:
  R.uint32(~S, ~next, s)

def int64(~S: Data, ~next: S -> W.U64 & S, s: S) -> W.U64 & S:
  R.int64(~S, ~next, s)

def int32(~S: Data, ~next: S -> W.U64 & S, s: S) -> U32 & S:
  R.int32(~S, ~next, s)

def uint64n(~S: Data, ~next: S -> W.U64 & S, s: S, +n: W.U64) -> W.U64 & S:
  R.uint64n(~S, ~next, s, n)

def uint_below(~S: Data, ~next: S -> W.U64 & S, s: S, +n: W.U64) -> W.U64 & S:
  R.uint64n(~S, ~next, s, n)

def uint32n(~S: Data, ~next: S -> W.U64 & S, s: S, +n: U32) -> U32 & S:
  R.uint32n(~S, ~next, s, n)

def intn(~S: Data, ~next: S -> W.U64 & S, s: S, +n: Nat) -> Nat & S:
  R.intn(~S, ~next, s, n)

def int_range(~S: Data, ~next: S -> W.U64 & S, s: S, +lo: Nat, +hi: Nat) -> Nat & S:
  R.int_range(~S, ~next, s, lo, hi)

def float64(~S: Data, ~next: S -> W.U64 & S, s: S) -> F.F64 & S:
  R.float64(~S, ~next, s)

def shuffle(~A: Data, ~S: Data, ~next: S -> W.U64 & S, s: S, +xs: List<&2, A>) -> List<&2, A> & S:
  R.shuffle(~A, ~S, ~next, s, xs)

def perm(~S: Data, ~next: S -> W.U64 & S, s: S, +n: Nat) -> List<&2, Nat> & S:
  R.perm(~S, ~next, s, n)

def shuffle_array(~A: Data, ~S: Data, ~next: S -> W.U64 & S, s: S, a: Array<A>, +n: Nat) -> Array<A> & S:
  R.shuffle_array(~A, ~S, ~next, s, a, n)
