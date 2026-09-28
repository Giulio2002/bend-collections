import Base
import ../../../src/math/u64.bend as W

# Executable specification of ChaCha8Rand, transcribed from C2SP
# chacha8rand (https://c2sp.org/chacha8rand, the generator of Go's
# math/rand/v2.ChaCha8 and runtime) and, for the ChaCha block function, from
# RFC 8439 sections 2.1-2.3 with eight rounds (Bernstein's ChaCha8). The
# state is the RFC's list x[0..15] of 32-bit words, indexed as in the RFC;
# nothing of the implementation is used except the neutral 64-bit word record
# W.U64{lo, hi}, the little-endian reading of eight output bytes.
#
#   quarter(x, a, b, c, d)   RFC 8439 2.1-2.2, on state indices
#   double_round(x)          RFC 8439 2.3 inner_block: columns, then diagonals
#   chacha8(key, ctr)        the ChaCha8 block: 4 double rounds, then the
#                            input state added word by word (RFC 8439 2.3)
#   c2sp_block(key, i)       C2SP: words 0..3 minus the constants, word 12
#                            minus the block number i
#   group(key, g)            C2SP's permutation of the four blocks g .. g + 3:
#                            for each word position, the word of each block
#   iteration(key)           the 1024 bytes (256 words) of one iteration
#   output(key), next_key(key)  its first 992 bytes and last 32 bytes
#   stream(n, key)           the first n 64-bit outputs of the generator
#                            keyed by key (words read little-endian in pairs)
#   key_of_seed(seed)        the eight little-endian words of a 32-byte seed
#                            (Go's byteorder.LEUint32), None unless 32 bytes
#                            below 256

def get(xs: List<&2, U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _:
      0
    case Con{x, rest} 0n:
      x
    case Con{x, rest} 1n+p:
      get(rest, p)

def put(xs: List<&2, U32>, i: Nat, y: U32) -> List<&2, U32>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{x, rest} 0n:
      Con{y, rest}
    case Con{x, rest} 1n+p:
      Con{x, put(rest, p, y)}

# x <<< n, 0 < n < 32
def rotl(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(32n, n)))

# RFC 8439 2.1: a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12;
# a += b; d ^= a; d <<<= 8; c += d; b ^= c; b <<<= 7 (2.2: on x[a..d])
def quarter(+x: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> List<&2, U32>:
  +a1 = U32.add(get(x, a), get(x, b))
  +d1 = rotl(U32.xor(get(x, d), a1), 16n)
  +c1 = U32.add(get(x, c), d1)
  +b1 = rotl(U32.xor(get(x, b), c1), 12n)
  +a2 = U32.add(a1, b1)
  +d2 = rotl(U32.xor(d1, a2), 8n)
  +c2 = U32.add(c1, d2)
  +b2 = rotl(U32.xor(b1, c2), 7n)
  put(put(put(put(x, a, a2), b, b2), c, c2), d, d2)

# RFC 8439 2.3 inner_block
def double_round(x: List<&2, U32>) -> List<&2, U32>:
  x1 = quarter(x, 0n, 4n, 8n, 12n)
  x2 = quarter(x1, 1n, 5n, 9n, 13n)
  x3 = quarter(x2, 2n, 6n, 10n, 14n)
  x4 = quarter(x3, 3n, 7n, 11n, 15n)
  x5 = quarter(x4, 0n, 5n, 10n, 15n)
  x6 = quarter(x5, 1n, 6n, 11n, 12n)
  x7 = quarter(x6, 2n, 7n, 8n, 13n)
  quarter(x7, 3n, 4n, 9n, 14n)

def double_rounds(n: Nat, x: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      x
    case 1n+p:
      double_rounds(p, double_round(x))

# "expand 32-byte k"
def constants() -> List<&2, U32>:
  [1634760805, 857760878, 2036477234, 1797285236]

def append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      Con{x, append(rest, ys)}

# RFC 8439 2.3: constants, key, block counter, nonce (here zero)
def initial(+key: List<&2, U32>, +ctr: U32) -> List<&2, U32>:
  append(constants(), append(key, [ctr, 0, 0, 0]))

def add_words(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Con{U32.add(x, y), add_words(xt, yt)}
    case _ _:
      Nil{}

# the ChaCha8 block function: eight rounds, then the input added back
def chacha8(+key: List<&2, U32>, +ctr: U32) -> List<&2, U32>:
  add_words(double_rounds(4n, initial(key, ctr)), initial(key, ctr))

def sub_at(+x: List<&2, U32>, +i: Nat, +c: U32) -> List<&2, U32>:
  put(x, i, U32.sub(get(x, i), c))

# C2SP: for each block, subtract the constants from words 0..3 and the block
# counter from word 12
def c2sp_block(+key: List<&2, U32>, +i: U32) -> List<&2, U32>:
  +b = chacha8(key, i)
  sub_at(sub_at(sub_at(sub_at(sub_at(b, 0n, 1634760805), 1n, 857760878), 2n, 2036477234), 3n, 1797285236), 12n, i)

# C2SP: "for each sequence of four blocks, first we output the first four
# bytes of each block, then the next four bytes of each block, and so on"
def interleave(k: Nat, +i: Nat, +b0: List<&2, U32>, +b1: List<&2, U32>, +b2: List<&2, U32>, +b3: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      []
    case 1n+p:
      Con{get(b0, i), Con{get(b1, i), Con{get(b2, i), Con{get(b3, i), interleave(p, Nat.add(i, 1n), b0, b1, b2, b3)}}}}

# the blocks g, g + 1, g + 2, g + 3, permuted
def group(+key: List<&2, U32>, +g: U32) -> List<&2, U32>:
  interleave(16n, 0n, c2sp_block(key, g), c2sp_block(key, U32.add(g, 1)), c2sp_block(key, U32.add(g, 2)), c2sp_block(key, U32.add(g, 3)))

# one iteration: the sixteen blocks 0..15, permuted, as 256 words
def iteration(+key: List<&2, U32>) -> List<&2, U32>:
  append(group(key, 0), append(group(key, 4), append(group(key, 8), group(key, 12))))

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      []
    case 1n+p Nil{}:
      []
    case 1n+p Con{x, rest}:
      Con{x, take(p, rest)}

def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      []
    case 1n+p Con{x, rest}:
      drop(p, rest)

# the first 992 bytes are output, the last 32 bytes key the next iteration
def output(+key: List<&2, U32>) -> List<&2, U32>:
  take(248n, iteration(key))

def next_key(+key: List<&2, U32>) -> List<&2, U32>:
  drop(248n, iteration(key))

# consecutive little-endian word pairs as 64-bit words
def words64(xs: List<&2, U32>) -> List<&2, W.U64>:
  match xs:
    case Con{lo, Con{hi, rest}}:
      Con{W.U64{lo, hi}, words64(rest)}
    case _:
      []

def head(xs: List<&2, W.U64>) -> W.U64:
  match xs:
    case Nil{}:
      W.U64{0, 0}
    case Con{x, rest}:
      x

def tail(xs: List<&2, W.U64>) -> List<&2, W.U64>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      rest

# n outputs: the words left of the current iteration, then the next
# iterations, each keyed by the last 32 bytes of the one before
def stream_go(n: Nat, buf: List<&2, W.U64>, +key: List<&2, U32>) -> List<&2, W.U64>:
  match n buf:
    case 0n _:
      []
    case 1n+p Con{x, rest}:
      Con{x, stream_go(p, rest, key)}
    case 1n+p Nil{}:
      Con{head(words64(output(key))), stream_go(p, tail(words64(output(key))), next_key(key))}

# the first n 64-bit outputs of ChaCha8Rand keyed by key (eight words)
def stream(n: Nat, +key: List<&2, U32>) -> List<&2, W.U64>:
  stream_go(n, [], key)

# Go's byteorder.LEUint32: b0 | b1 << 8 | b2 << 16 | b3 << 24
def le32(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.shln(b2, 16n)), U32.shln(b3, 24n))

def bytes_ok(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+b, rest}:
      Bool.and(U32.is_lt(b, 256), bytes_ok(rest))

def words_of(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Con{b0, Con{b1, Con{b2, Con{b3, rest}}}}:
      Con{le32(b0, b1, b2, b3), words_of(rest)}
    case _:
      []

def length(bs: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, rest}:
      1n+length(rest)

def key_if(+bs: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{words_of(bs)}
    case False{}:
      None{}

# the key of a seed: 32 bytes, each below 256
def key_of_seed(+seed: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  key_if(seed, Bool.and(Nat.is_eq(length(seed), 32n), bytes_ok(seed)))
