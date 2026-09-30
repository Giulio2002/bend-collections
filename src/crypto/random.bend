import Base
import ../math/u64.bend as W
import ../math/w64.bend as X
import ../math/random/rand.bend as R
import ../math/random/chacha8.bend as C8
import ../math/random/chacha8/block.bend as B

# A cryptographically secure random generator: ChaCha8Rand (C2SP
# chacha8rand), the generator behind Go's runtime and math/rand/v2 top-level
# functions and its ChaCha8 source, with Go's ChaCha8.Read byte order.
#
#   new(seed)           Some{g} for a 32-byte seed (32 bytes < 256), None
#                       otherwise: deterministic, for tests and reproducible
#                       runs; the seed must be secret and uniformly random
#   from_os()           IO: a generator keyed with 32 bytes of operating-system
#                       entropy (eight IO.random_u32 calls: getrandom /
#                       arc4random / crypto.getRandomValues)
#   bytes(g, n)         n random bytes (a list of U32 < 256) and the new
#                       generator; Go's (*ChaCha8).Read: the little-endian
#                       bytes of successive 64-bit outputs, a partly used
#                       output's remaining bytes served first by the next call
#   uint64(g)           a uniform 64-bit word
#   uint_below(g, n)    uniform in [0, n) for n > 0 (Lemire, unbiased)
#   shuffle(g, items)   a uniform permutation of items (Fisher-Yates)
#   next(g)             the Source step, for every function of
#                       src/math/random/rand.bend: R.float64(~Gen, ~next, g)
#
# Security (the C2SP chacha8rand design; Aumasson, "Too Much Crypto", for
# eight rounds): the output is ChaCha8 keyed by the seed, a PRF, so it is
# indistinguishable from uniform to anyone who does not know the seed.
# Every 992 bytes of output the key is replaced by 32 bytes of the stream
# (fast key erasure), so once a key is overwritten the outputs before it
# cannot be recomputed from the generator's state: forward secrecy with a
# window of at most one iteration (the unread words of the current
# iteration and the key it started from are in the state). Callers must:
#
#   - keep the seed and every generator value secret (a copied generator
#     repeats its outputs: Bend values are immutable, so reusing an old g
#     replays the same bytes; always continue from the returned generator);
#   - seed from_os() for secrets; new(seed) only with a secret uniform seed;
#   - not rely on constant-time behaviour: Bend has no timing model, and
#     uint_below's rejection loop takes a data-dependent number of draws (as
#     in Go), which reveals nothing about the accepted value.
#
# The stream is proved to be C2SP's for every seed, uint_below < n, the
# rejection exactly unbiased and shuffle a permutation
# (proofs/crypto/random/); tested against Go's vectors (tools/check_random.py).

type Gen is Data:
  G{src: C8.ChaCha8, pending: List<&2, U32>}

def wrap(m: Maybe<&2, C8.ChaCha8>) -> Maybe<&2, Gen>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{G{c, []}}

def new(+seed: List<&2, U32>) -> Maybe<&2, Gen>:
  wrap(C8.new(seed))

def of_words(+k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32) -> Gen:
  G{C8.of_key(B.K{k0, k1, k2, k3, k4, k5, k6, k7}), []}

def os_word() -> IO(U32):
  IO.try(U32, IO.random_u32())

def from_os() -> IO(Gen):
  do IO<Gen>:
    k0 : U32 <- os_word()
    k1 : U32 <- os_word()
    k2 : U32 <- os_word()
    k3 : U32 <- os_word()
    k4 : U32 <- os_word()
    k5 : U32 <- os_word()
    k6 : U32 <- os_word()
    k7 : U32 <- os_word()
    return of_words(k0, k1, k2, k3, k4, k5, k6, k7)

def keep_pending(+p: List<&2, U32>, r: W.U64 & C8.ChaCha8) -> W.U64 & Gen:
  (x, c) = r
  (x, G{c, p})

# the Source step: the next 64-bit output (pending bytes are left for bytes)
def next(g: Gen) -> W.U64 & Gen:
  match g:
    case G{c, +p}:
      keep_pending(p, C8.next(c))

# the eight little-endian bytes of a 64-bit word
def le_bytes(+x: W.U64) -> List<&2, U32>:
  +l = X.lo(x)
  +h = X.hi(x)
  [U32.and(l, 255), U32.and(U32.shrn(l, 8n), 255), U32.and(U32.shrn(l, 16n), 255), U32.and(U32.shrn(l, 24n), 255), U32.and(h, 255), U32.and(U32.shrn(h, 8n), 255), U32.and(U32.shrn(h, 16n), 255), U32.and(U32.shrn(h, 24n), 255)]

# the bytes read so far (latest first), the generator and its pending bytes
type Fill is Data:
  FS{acc: List<&2, U32>, src: C8.ChaCha8, pending: List<&2, U32>}

def split_bytes(acc: List<&2, U32>, c: C8.ChaCha8, bs: List<&2, U32>) -> Fill:
  match bs:
    case Con{b, rest}:
      FS{Con{b, acc}, c, rest}
    case Nil{}:
      FS{acc, c, []}

def split(acc: List<&2, U32>, r: W.U64 & C8.ChaCha8) -> Fill:
  (+x, c) = r
  split_bytes(acc, c, le_bytes(x))

# one byte: the next pending byte, or the first byte of a fresh word
def take1(f: Fill) -> Fill:
  match f:
    case FS{acc, c, p}:
      match p:
        case Con{b, rest}:
          FS{Con{b, acc}, c, rest}
        case Nil{}:
          split(acc, C8.next(c))

# n bytes, one at a time (the definition bytes is proved against)
def fill(n: Nat, f: Fill) -> Fill:
  match n:
    case 0n:
      f
    case 1n+k:
      fill(k, take1(f))

# the eight bytes of a fresh word at once (what split and seven take1 give)
def word(acc: List<&2, U32>, r: W.U64 & C8.ChaCha8) -> Fill:
  (+x, c) = r
  +l = X.lo(x)
  +h = X.hi(x)
  FS{Con{U32.and(U32.shrn(h, 24n), 255), Con{U32.and(U32.shrn(h, 16n), 255), Con{U32.and(U32.shrn(h, 8n), 255), Con{U32.and(h, 255), Con{U32.and(U32.shrn(l, 24n), 255), Con{U32.and(U32.shrn(l, 16n), 255), Con{U32.and(U32.shrn(l, 8n), 255), Con{U32.and(l, 255), acc}}}}}}}}, c, []}

# fill, a whole word at a time while no bytes are pending (same bytes)
def fill_fast(n: Nat, f: Fill) -> Fill:
  match n f:
    case 8n+k FS{acc, c, p}:
      match p:
        case Nil{}:
          fill_fast(k, word(acc, C8.next(c)))
        case Con{b, rest}:
          fill_fast(7n+k, FS{Con{b, acc}, c, rest})
    case 1n+k g:
      fill_fast(k, take1(g))
    case 0n g:
      g

def done(f: Fill) -> List<&2, U32> & Gen:
  match f:
    case FS{acc, c, p}:
      (List.reverse(&2, U32, acc), G{c, p})

def bytes(g: Gen, n: Nat) -> List<&2, U32> & Gen:
  match g:
    case G{c, p}:
      done(fill_fast(n, FS{[], c, p}))

def uint64(g: Gen) -> W.U64 & Gen:
  next(g)

# uniform in [0, n) for n > 0
def uint_below(g: Gen, +n: W.U64) -> W.U64 & Gen:
  R.uint64n(~Gen, ~next, g, n)

# a uniform permutation of items
def shuffle(~A: Data, g: Gen, +items: List<&2, A>) -> List<&2, A> & Gen:
  R.shuffle(~A, ~Gen, ~next, g, items)
