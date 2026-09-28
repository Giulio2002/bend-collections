import Base
import ../../src/crypto/sha512/types.bend as T

# Executable specification of SHA-512 (FIPS 180-4), byte oriented, written
# from the standard in the shape of spec/crypto/sha.bend (SHA-256) and of
# HACL*'s Spec.SHA2. Only the neutral records of src/crypto/sha512/types.bend
# are shared with the implementation: a 64-bit word is T.W{hi, lo}, its two
# 32-bit halves, most significant first, and the working state is T.H{a..h}.
# No implementation function, table or padding is called.
#
# Bytes are U32 values; each contributes its low 8 bits (the byte convention
# of the crypto modules: every byte < 256).

# ---------------------------------------------------------------- 64-bit words

# FIPS 180-4 section 3.2: x + y mod 2^64. The low halves add modulo 2^32; the
# high halves add the carry out of the low half, which is 1 exactly when the
# low sum wrapped below either addend.
def add(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{ah, +al} T.W{bh, bl}:
      +lo = U32.add(al, bl)
      T.W{U32.add(U32.add(ah, bh), Bool.to_u32(U32.is_lt(lo, al))), lo}

def xor(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{ah, al} T.W{bh, bl}:
      T.W{U32.xor(ah, bh), U32.xor(al, bl)}

def and(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{ah, al} T.W{bh, bl}:
      T.W{U32.and(ah, bh), U32.and(al, bl)}

def not(a: T.Lane) -> T.Lane:
  match a:
    case T.W{ah, al}:
      T.W{U32.not(ah), U32.not(al)}

# ROTR^n on the halves for 0 < n < 32: each half keeps its bits shifted right
# and takes the other half's low n bits at the top.
def rotr_small(+hi: U32, +lo: U32, +n: Nat) -> T.Lane:
  T.W{U32.or(U32.shrn(hi, n), U32.shln(lo, Nat.sub(32n, n))),
    U32.or(U32.shrn(lo, n), U32.shln(hi, Nat.sub(32n, n)))}

# 32 <= n < 64: rotating by 32 swaps the halves, then rotate by n - 32.
def rotr_split(+hi: U32, +lo: U32, +n: Nat, small: Bool) -> T.Lane:
  match small:
    case True{}:
      rotr_small(hi, lo, n)
    case False{}:
      rotr_small(lo, hi, Nat.sub(n, 32n))

# FIPS 180-4 section 3.2: ROTR^n(x) = (x >> n) OR (x << 64 - n), 0 < n < 64.
def rotr(x: T.Lane, +n: Nat) -> T.Lane:
  match x:
    case T.W{+hi, +lo}:
      rotr_split(hi, lo, n, Nat.is_lt(n, 32n))

# FIPS 180-4 section 3.2: SHR^n(x) = x >> n, here for 0 < n < 32.
def shr(x: T.Lane, +n: Nat) -> T.Lane:
  match x:
    case T.W{+hi, +lo}:
      T.W{U32.shrn(hi, n), U32.or(U32.shrn(lo, n), U32.shln(hi, Nat.sub(32n, n)))}

# ---------------------------------------------------------------- section 4.1.3

def sum0(+x: T.Lane) -> T.Lane:
  xor(xor(rotr(x, 28n), rotr(x, 34n)), rotr(x, 39n))

def sum1(+x: T.Lane) -> T.Lane:
  xor(xor(rotr(x, 14n), rotr(x, 18n)), rotr(x, 41n))

def sigma0(+x: T.Lane) -> T.Lane:
  xor(xor(rotr(x, 1n), rotr(x, 8n)), shr(x, 7n))

def sigma1(+x: T.Lane) -> T.Lane:
  xor(xor(rotr(x, 19n), rotr(x, 61n)), shr(x, 6n))

def ch(+x: T.Lane, y: T.Lane, z: T.Lane) -> T.Lane:
  xor(and(x, y), and(not(x), z))

def maj(+x: T.Lane, +y: T.Lane, +z: T.Lane) -> T.Lane:
  xor(xor(and(x, y), and(x, z)), and(y, z))

# ---------------------------------------------------------------- constants

# Section 5.3.5: the initial hash value H(0).
def initial() -> T.State:
  T.H{T.W{1779033703, 4089235720}, T.W{3144134277, 2227873595},
    T.W{1013904242, 4271175723}, T.W{2773480762, 1595750129},
    T.W{1359893119, 2917565137}, T.W{2600822924, 725511199},
    T.W{528734635, 4215389547}, T.W{1541459225, 327033209}}

# Section 4.2.3: K0 .. K79.
def constants() -> List<&2, T.Lane>:
  [T.W{1116352408, 3609767458}, T.W{1899447441, 602891725},
   T.W{3049323471, 3964484399}, T.W{3921009573, 2173295548},
   T.W{961987163, 4081628472}, T.W{1508970993, 3053834265},
   T.W{2453635748, 2937671579}, T.W{2870763221, 3664609560},
   T.W{3624381080, 2734883394}, T.W{310598401, 1164996542},
   T.W{607225278, 1323610764}, T.W{1426881987, 3590304994},
   T.W{1925078388, 4068182383}, T.W{2162078206, 991336113},
   T.W{2614888103, 633803317}, T.W{3248222580, 3479774868},
   T.W{3835390401, 2666613458}, T.W{4022224774, 944711139},
   T.W{264347078, 2341262773}, T.W{604807628, 2007800933},
   T.W{770255983, 1495990901}, T.W{1249150122, 1856431235},
   T.W{1555081692, 3175218132}, T.W{1996064986, 2198950837},
   T.W{2554220882, 3999719339}, T.W{2821834349, 766784016},
   T.W{2952996808, 2566594879}, T.W{3210313671, 3203337956},
   T.W{3336571891, 1034457026}, T.W{3584528711, 2466948901},
   T.W{113926993, 3758326383}, T.W{338241895, 168717936},
   T.W{666307205, 1188179964}, T.W{773529912, 1546045734},
   T.W{1294757372, 1522805485}, T.W{1396182291, 2643833823},
   T.W{1695183700, 2343527390}, T.W{1986661051, 1014477480},
   T.W{2177026350, 1206759142}, T.W{2456956037, 344077627},
   T.W{2730485921, 1290863460}, T.W{2820302411, 3158454273},
   T.W{3259730800, 3505952657}, T.W{3345764771, 106217008},
   T.W{3516065817, 3606008344}, T.W{3600352804, 1432725776},
   T.W{4094571909, 1467031594}, T.W{275423344, 851169720},
   T.W{430227734, 3100823752}, T.W{506948616, 1363258195},
   T.W{659060556, 3750685593}, T.W{883997877, 3785050280},
   T.W{958139571, 3318307427}, T.W{1322822218, 3812723403},
   T.W{1537002063, 2003034995}, T.W{1747873779, 3602036899},
   T.W{1955562222, 1575990012}, T.W{2024104815, 1125592928},
   T.W{2227730452, 2716904306}, T.W{2361852424, 442776044},
   T.W{2428436474, 593698344}, T.W{2756734187, 3733110249},
   T.W{3204031479, 2999351573}, T.W{3329325298, 3815920427},
   T.W{3391569614, 3928383900}, T.W{3515267271, 566280711},
   T.W{3940187606, 3454069534}, T.W{4118630271, 4000239992},
   T.W{116418474, 1914138554}, T.W{174292421, 2731055270},
   T.W{289380356, 3203993006}, T.W{460393269, 320620315},
   T.W{685471733, 587496836}, T.W{852142971, 1086792851},
   T.W{1017036298, 365543100}, T.W{1126000580, 2618297676},
   T.W{1288033470, 3409855158}, T.W{1501505948, 4234509866},
   T.W{1607167915, 987167468}, T.W{1816402316, 1246189591}]

# ---------------------------------------------------------------- section 5.1.2: padding

# A base-256 representation, most significant digit first, of fixed width.
def octets(width: Nat, +n: Nat) -> List<&2, U32>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, octets(p, Nat.div(n, 256n)),
        [U32.from_nat(Nat.mod(n, 256n))])

# The 128-bit block of the message length in bits, 8n: its low octet is
# 8 * (n mod 32) and the fifteen above it are n div 32 in base 256
# (8n = 256 * (n div 32) + 8 * (n mod 32)), so no Nat above n is formed.
def length_field(+n: Nat) -> List<&2, U32>:
  List.append(&2, U32, octets(15n, Nat.div(n, 32n)),
    [U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n)])

# The k zero bytes with n + 1 + k = 112 (mod 128): a remainder of 0..111 leaves
# room for the length in this block, one of 112..127 needs another block.
def zero_count_if(r: Nat, fits: Bool) -> Nat:
  match fits:
    case True{}:
      Nat.sub(111n, r)
    case False{}:
      Nat.sub(239n, r)

def zero_count(+r: Nat) -> Nat:
  zero_count_if(r, Nat.is_le(r, 111n))

def padding_suffix(+n: Nat) -> List<&2, U32>:
  128 <> List.append(&2, U32,
    List.replicate(U32, zero_count(Nat.mod(n, 128n)), 0), length_field(n))

def pad(+bytes: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, bytes, padding_suffix(List.length(&2, U32, bytes)))

# ---------------------------------------------------------------- section 5.2.2: parsing

def decode(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.or(U32.shln(U32.and(a, 255), 24n),
    U32.shln(U32.and(b, 255), 16n)), U32.shln(U32.and(c, 255), 8n)), U32.and(d, 255))

# Big-endian 64-bit words, eight bytes each (a trailing partial word is dropped;
# padded messages have none).
def words(bytes: List<&2, U32>) -> List<&2, T.Lane>:
  match bytes:
    case a <> b <> c <> d <> e <> f <> g <> h <> rest:
      T.W{decode(a, b, c, d), decode(e, f, g, h)} <> words(rest)
    case _:
      Nil{}

# ---------------------------------------------------------------- section 6.4.2: the schedule

# In reverse history, index j is W[t-1-j]; the zero default makes nth total.
def nth(history: List<&2, T.Lane>, index: Nat) -> T.Lane:
  match history index:
    case Nil{} _:
      T.W{0, 0}
    case w <> rest 0n:
      w
    case w <> rest 1n+p:
      nth(rest, p)

def previous(history: List<&2, T.Lane>, lag: Nat) -> T.Lane:
  nth(history, Nat.sub(lag, 1n))

# W[t] = sigma1(W[t-2]) + W[t-7] + sigma0(W[t-15]) + W[t-16]
def recurrence(+history: List<&2, T.Lane>) -> T.Lane:
  add(add(add(sigma1(previous(history, 2n)), previous(history, 7n)),
    sigma0(previous(history, 15n))), previous(history, 16n))

def extension(rounds: Nat, +history: List<&2, T.Lane>) -> List<&2, T.Lane>:
  match rounds:
    case 0n:
      Nil{}
    case 1n+p:
      +w = recurrence(history)
      w <> extension(p, w <> history)

# SHA-512 instantiates extra = 64, extending the 16 block words to 80.
def schedule(extra: Nat, +block: List<&2, T.Lane>) -> List<&2, T.Lane>:
  List.append(&2, T.Lane, block, extension(extra, List.reverse(&2, T.Lane, block)))

def schedules(ws: List<&2, T.Lane>, +extra: Nat) -> List<&2, List<&2, T.Lane>>:
  match ws:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> rest:
      schedule(extra, [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]) <> schedules(rest, extra)
    case _:
      Nil{}

def prepare(bytes: List<&2, U32>, extra: Nat) -> List<&2, List<&2, T.Lane>>:
  schedules(words(pad(bytes)), extra)

# ---------------------------------------------------------------- section 6.4.2: the rounds

def step(s: T.State, k: T.Lane, w: T.Lane) -> T.State:
  T.H{+a, +b, +c, d, +e, +f, +g, h} = s
  +t1 = add(add(add(add(h, sum1(e)), ch(e, f, g)), k), w)
  t2 = add(sum0(a), maj(a, b, c))
  T.H{add(t1, t2), a, b, c, add(d, t1), e, f, g}

def rounds(ks: List<&2, T.Lane>, ws: List<&2, T.Lane>) -> T.State -> T.State:
  match ks ws:
    case Nil{} _:
      s => s
    case k <> kt Nil{}:
      s => s
    case k <> kt w <> wt:
      next = rounds(kt, wt)
      s => next(step(s, k, w))

def feedforward(x: T.State, y: T.State) -> T.State:
  T.H{a, b, c, d, e, f, g, h} = x
  T.H{i, j, k, l, m, n, o, p} = y
  T.H{add(a, i), add(b, j), add(c, k), add(d, l), add(e, m), add(f, n), add(g, o), add(h, p)}

def compress(ws: List<&2, T.Lane>, ks: List<&2, T.Lane>, +s: T.State) -> T.State:
  feedforward(s, rounds(ks, ws)(s))

def blocks(prepared: List<&2, List<&2, T.Lane>>, +ks: List<&2, T.Lane>) -> T.State -> T.State:
  match prepared:
    case Nil{}:
      s => s
    case block <> rest:
      next = blocks(rest, ks)
      s => next(compress(block, ks, s))

def digest(s: T.State) -> List<&2, T.Lane>:
  T.H{a, b, c, d, e, f, g, h} = s
  [a, b, c, d, e, f, g, h]

def hash(bytes: List<&2, U32>, extra: Nat, ks: List<&2, T.Lane>) -> List<&2, T.Lane>:
  digest(blocks(prepare(bytes, extra), ks)(initial()))

# SHA-512(M): the eight words H(N).
def sha512(bytes: List<&2, U32>) -> List<&2, T.Lane>:
  hash(bytes, 64n, constants())

# ---------------------------------------------------------------- the digest as bytes

# Each word most significant octet first.
def word_octets(w: T.Lane) -> List<&2, U32>:
  match w:
    case T.W{+hi, +lo}:
      [U32.and(U32.shrn(hi, 24n), 255), U32.and(U32.shrn(hi, 16n), 255),
       U32.and(U32.shrn(hi, 8n), 255), U32.and(hi, 255),
       U32.and(U32.shrn(lo, 24n), 255), U32.and(U32.shrn(lo, 16n), 255),
       U32.and(U32.shrn(lo, 8n), 255), U32.and(lo, 255)]

def digest_octets(ws: List<&2, T.Lane>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> tail:
      List.append(&2, U32, word_octets(w), digest_octets(tail))

# The 64-byte SHA-512 digest.
def sha512_bytes(bytes: List<&2, U32>) -> List<&2, U32>:
  digest_octets(sha512(bytes))
