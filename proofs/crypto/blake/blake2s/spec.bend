import Base
import ../../../../src/crypto/blake/blake2s/types.bend as T

# Executable specification of unkeyed BLAKE2s-256, written from RFC 7693.
# Only the neutral chaining-value record T.State is shared with the
# implementation; no implementation function is called. The work vector,
# the message block and SIGMA are lists indexed as in the RFC, and the message
# is handled byte by byte: the packed input is read as little-endian bytes,
# the final block is zero-padded byte-wise, and block words are reassembled
# from bytes (RFC 7693 section 2.4, "little-endian byte order").

# ---------------------------------------------------------------- 2.6 constants

# IV[0..7] = 0x6A09E667 0xBB67AE85 0x3C6EF372 0xA54FF53A
#            0x510E527F 0x9B05688C 0x1F83D9AB 0x5BE0CD19
def iv() -> List<&2,U32>:
  [1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225]

# SIGMA[i mod 10].
def sigma(r: Nat) -> List<&2,Nat>:
  match r:
    case 0n: [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n]
    case 1n: [14n, 10n, 4n, 8n, 9n, 15n, 13n, 6n, 1n, 12n, 0n, 2n, 11n, 7n, 5n, 3n]
    case 2n: [11n, 8n, 12n, 0n, 5n, 2n, 15n, 13n, 10n, 14n, 3n, 6n, 7n, 1n, 9n, 4n]
    case 3n: [7n, 9n, 3n, 1n, 13n, 12n, 11n, 14n, 2n, 6n, 5n, 10n, 4n, 0n, 15n, 8n]
    case 4n: [9n, 0n, 5n, 7n, 2n, 4n, 10n, 15n, 14n, 1n, 11n, 12n, 6n, 8n, 3n, 13n]
    case 5n: [2n, 12n, 6n, 10n, 0n, 11n, 8n, 3n, 4n, 13n, 7n, 5n, 15n, 14n, 1n, 9n]
    case 6n: [12n, 5n, 1n, 15n, 14n, 13n, 4n, 10n, 0n, 7n, 6n, 3n, 9n, 2n, 8n, 11n]
    case 7n: [13n, 11n, 7n, 14n, 12n, 1n, 3n, 9n, 5n, 0n, 15n, 4n, 8n, 6n, 2n, 10n]
    case 8n: [6n, 15n, 14n, 9n, 11n, 3n, 0n, 8n, 12n, 2n, 13n, 7n, 1n, 4n, 10n, 5n]
    case 9n: [10n, 2n, 8n, 4n, 7n, 6n, 1n, 5n, 15n, 11n, 9n, 14n, 3n, 12n, 13n, 0n]
    case 10n+p: sigma(p)

# ---------------------------------------------------------------- list indexing

def get(xs: List<&2,U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _: 0
    case x <> rest 0n: x
    case x <> rest 1n+p: get(rest, p)

def index(xs: List<&2,Nat>, i: Nat) -> Nat:
  match xs i:
    case Nil{} _: 0n
    case x <> rest 0n: x
    case x <> rest 1n+p: index(rest, p)

def put(xs: List<&2,U32>, i: Nat, y: U32) -> List<&2,U32>:
  match xs i:
    case Nil{} _: Nil{}
    case x <> rest 0n: y <> rest
    case x <> rest 1n+p: x <> put(rest, p, y)

# ---------------------------------------------------------------- 3.1 G

# x >>> n: rotation of a 32-bit word right by n bits (0 < n < 32).
def rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

# G(v[0..15], a, b, c, d, x, y) with BLAKE2s rotations R1..R4 = 16, 12, 8, 7.
def mix(+v: List<&2,U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, x: U32, y: U32) -> List<&2,U32>:
  +va = U32.add(U32.add(get(v, a), get(v, b)), x)
  +vd = rotr(U32.xor(get(v, d), va), 16n)
  +vc = U32.add(get(v, c), vd)
  +vb = rotr(U32.xor(get(v, b), vc), 12n)
  +va2 = U32.add(U32.add(va, vb), y)
  +vd2 = rotr(U32.xor(vd, va2), 8n)
  +vc2 = U32.add(vc, vd2)
  +vb2 = rotr(U32.xor(vb, vc2), 7n)
  put(put(put(put(v, a, va2), b, vb2), c, vc2), d, vd2)

# ---------------------------------------------------------------- 3.2 F

# One round with schedule s: four column steps, then four diagonal steps.
def round(v: List<&2,U32>, +s: List<&2,Nat>, +m: List<&2,U32>) -> List<&2,U32>:
  v1 = mix(v, 0n, 4n, 8n, 12n, get(m, index(s, 0n)), get(m, index(s, 1n)))
  v2 = mix(v1, 1n, 5n, 9n, 13n, get(m, index(s, 2n)), get(m, index(s, 3n)))
  v3 = mix(v2, 2n, 6n, 10n, 14n, get(m, index(s, 4n)), get(m, index(s, 5n)))
  v4 = mix(v3, 3n, 7n, 11n, 15n, get(m, index(s, 6n)), get(m, index(s, 7n)))
  v5 = mix(v4, 0n, 5n, 10n, 15n, get(m, index(s, 8n)), get(m, index(s, 9n)))
  v6 = mix(v5, 1n, 6n, 11n, 12n, get(m, index(s, 10n)), get(m, index(s, 11n)))
  v7 = mix(v6, 2n, 7n, 8n, 13n, get(m, index(s, 12n)), get(m, index(s, 13n)))
  mix(v7, 3n, 4n, 9n, 14n, get(m, index(s, 14n)), get(m, index(s, 15n)))

# Rounds i, i+1, ..., i+n-1.
def rounds(n: Nat, +i: Nat, v: List<&2,U32>, +m: List<&2,U32>) -> List<&2,U32>:
  match n:
    case 0n: v
    case 1n+p: rounds(p, 1n+i, round(v, sigma(i), m), m)

def invert(last: Bool, +v: List<&2,U32>) -> List<&2,U32>:
  match last:
    case True{}: put(v, 14n, U32.xor(get(v, 14n), 4294967295))
    case False{}: v

# F(h, m, t, f) with r rounds (r = 10 for BLAKE2s): t = t0 + 2^32 * t1 is the
# byte counter, f the final-block flag.
def compress(+r: Nat, h: T.State, +m: List<&2,U32>, +t0: U32, +t1: U32, last: Bool) -> T.State:
  match h:
    case T.H{+h0, +h1, +h2, +h3, +h4, +h5, +h6, +h7}:
      +v0 = List.append(&2, U32, [h0, h1, h2, h3, h4, h5, h6, h7], iv())
      +v1 = put(v0, 12n, U32.xor(get(v0, 12n), t0))
      +v2 = put(v1, 13n, U32.xor(get(v1, 13n), t1))
      +v = rounds(r, 0n, invert(last, v2), m)
      T.H{U32.xor(U32.xor(h0, get(v, 0n)), get(v, 8n)),
          U32.xor(U32.xor(h1, get(v, 1n)), get(v, 9n)),
          U32.xor(U32.xor(h2, get(v, 2n)), get(v, 10n)),
          U32.xor(U32.xor(h3, get(v, 3n)), get(v, 11n)),
          U32.xor(U32.xor(h4, get(v, 4n)), get(v, 12n)),
          U32.xor(U32.xor(h5, get(v, 5n)), get(v, 13n)),
          U32.xor(U32.xor(h6, get(v, 6n)), get(v, 14n)),
          U32.xor(U32.xor(h7, get(v, 7n)), get(v, 15n))}

# ---------------------------------------------------------------- 2.4 bytes

# Byte k (0 = least significant) of a word: the packed input holds four
# message bytes per word in little-endian order.
def byte(+w: U32, k: Nat) -> U32:
  U32.and(255, U32.shrn(w, Nat.mul(8n, k)))

def octets(+w: U32) -> List<&2,U32>:
  [byte(w, 0n), byte(w, 1n), byte(w, 2n), byte(w, 3n)]

def serialize(ws: List<&2,U32>) -> List<&2,U32>:
  match ws:
    case Nil{}: Nil{}
    case w <> rest: List.append(&2, U32, octets(w), serialize(rest))

# Zero padding: the byte at message offset i survives only when i < length.
def keep_if(inside: Bool, b: U32) -> U32:
  match inside:
    case True{}: b
    case False{}: 0

def pad(bytes: List<&2,U32>, +i: Nat, +length: Nat) -> List<&2,U32>:
  match bytes:
    case Nil{}: Nil{}
    case b <> rest: keep_if(Nat.is_lt(i, length), b) <> pad(rest, 1n+i, length)

# A block word from four bytes, least significant first.
def word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.shln(b2, 16n)), U32.shln(b3, 24n))

def words(bytes: List<&2,U32>) -> List<&2,U32>:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> rest: word(b0, b1, b2, b3) <> words(rest)
    case _: Nil{}

# ---------------------------------------------------------------- 3.3 BLAKE2s

# The byte counter t as two 32-bit halves: t + n, with the carry into t1.
def carry(c: Bool, hi: U32) -> U32:
  match c:
    case True{}: U32.add(hi, 1)
    case False{}: hi

def count_hi(+lo: U32, hi: U32, +n: U32) -> U32:
  carry(U32.is_lt(U32.add(lo, n), n), hi)

# Read the sixteen words of the block at word offset base, in order.
def gather(n: Nat, +base: U32, +next: U32, acc: List<&2,U32>, pair: Array<U32> & U32) -> Array<U32> & List<&2,U32>:
  match n pair:
    case 0n Tuple{a, w}: (a, List.reverse(&2, U32, w <> acc))
    case 1n+p Tuple{a, w}: gather(p, base, U32.inc(next), w <> acc, Array.get(U32, a, U32.add(base, next)))

def read_block(a: Array<U32>, +base: U32) -> Array<U32> & List<&2,U32>:
  gather(15n, base, 1, [], Array.get(U32, a, base))

# A block before the last: all 64 bytes are message bytes.
def full_block(+r: Nat, pair: Array<U32> & List<&2,U32>, h: T.State, +t0: U32, +t1: U32) -> Array<U32> & T.State:
  (a, ws) = pair
  (a, compress(r, h, words(serialize(ws)), t0, t1, False{}))

# The last block: the remaining bytes, zero-padded to 64.
def last_block(+r: Nat, pair: Array<U32> & List<&2,U32>, +remain: Nat, h: T.State, +t0: U32, +t1: U32) -> T.State:
  (a, ws) = pair
  compress(r, h, words(pad(serialize(ws), 0n, remain)), t0, t1, True{})

def absorb(+r: Nat, a: Array<U32>, +base: U32, h: T.State, +t0: U32, +t1: U32) -> Array<U32> & T.State:
  full_block(r, read_block(a, base), h, t0, t1)

def finish(+r: Nat, a: Array<U32>, +base: U32, +t0: U32, t1: U32, +remain: Nat, h: T.State) -> T.State:
  +n = U32.from_nat(remain)
  last_block(r, read_block(a, base), remain, h, U32.add(t0, n), count_hi(t0, t1, n))

# n full blocks, then the last one; t counts the bytes compressed so far.
def blocks(+r: Nat, n: Nat, +base: U32, +t0: U32, t1: U32, +remain: Nat, pair: Array<U32> & T.State) -> T.State:
  match n pair:
    case 0n Tuple{a, h}: finish(r, a, base, t0, t1, remain, h)
    case 1n+p Tuple{a, h}:
      +c0 = U32.add(t0, 64)
      +c1 = count_hi(t0, t1, 64)
      blocks(r, p, U32.add(base, 16), c0, c1, remain, absorb(r, a, base, h, c0, c1))

# h[0..7] := IV[0..7]; h[0] ^= 0x01010000 ^ (kk << 8) ^ nn with kk = 0, nn = 32.
def initial() -> T.State:
  T.H{U32.xor(1779033703, U32.xor(16842752, 32)), 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

# dd = ceil(ll / 64) blocks, and dd = 1 for the empty message.
def block_count(+ll: Nat) -> Nat:
  match ll:
    case 0n: 1n
    case 1n+p: Nat.div(Nat.add(ll, 63n), 64n)

def hash(+r: Nat, a: Array<U32>, +ll: Nat) -> T.State:
  +n = Nat.sub(block_count(ll), 1n)
  blocks(r, n, 0, 0, 0, Nat.sub(ll, Nat.mul(64n, n)), (a, initial()))

# The 32-byte digest as eight little-endian words, in a fresh 8-slot array.
def digest(h: T.State) -> Array<U32>:
  match h:
    case T.H{h0, h1, h2, h3, h4, h5, h6, h7}:
      ANode{ANode{ANode{ALeaf{h0}, ALeaf{h1}}, ANode{ALeaf{h2}, ALeaf{h3}}}, ANode{ANode{ALeaf{h4}, ALeaf{h5}}, ANode{ALeaf{h6}, ALeaf{h7}}}}

def checked(+r: Nat, valid: Bool, a: Array<U32>, ll: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(hash(r, a, ll))}

def sized(+r: Nat, +ll: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a, capacity) = pair
  checked(r, Nat.is_le(ll, Nat.mul(4n, U32.to_nat(capacity))), a, ll)

# The hash with r rounds per compression, of the first ll bytes of the packed
# array a; None when ll exceeds the 4 * capacity bytes the array holds.
def blake2s_rounds(+r: Nat, a: Array<U32>, ll: Nat) -> Maybe<&1,Array<U32>>:
  sized(r, ll, Array.size(U32, a))

# BLAKE2s-256: r = 10.
def blake2s(a: Array<U32>, ll: Nat) -> Maybe<&1,Array<U32>>:
  blake2s_rounds(10n, a, ll)
