import Base
import ../../src/crypto/sha/state.bend as Types

# Executable specification of the byte-oriented SHA-256 algorithm in FIPS 180-4.
# Only the neutral state representation is shared with the implementation.
# No implementation arithmetic, padding, schedule, table, or hash is called.
# Base U32 has the required modulo-2^32 arithmetic and logical bit operations.

def initial() -> Types.State:
  Types.H{1779033703, 3144134277, 1013904242, 2773480762,
    1359893119, 2600822924, 528734635, 1541459225}

# FIPS 4.1.2: ROR_n(x) = SHR_n(x) OR SHL_(32-n)(x).
def rotate(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def sigma0(+x: U32) -> U32:
  U32.xor(U32.xor(rotate(x, 7n), rotate(x, 18n)), U32.shrn(x, 3n))

def sigma1(+x: U32) -> U32:
  U32.xor(U32.xor(rotate(x, 17n), rotate(x, 19n)), U32.shrn(x, 10n))

def sum0(+x: U32) -> U32:
  U32.xor(U32.xor(rotate(x, 2n), rotate(x, 13n)), rotate(x, 22n))

def sum1(+x: U32) -> U32:
  U32.xor(U32.xor(rotate(x, 6n), rotate(x, 11n)), rotate(x, 25n))

def ch(+x: U32, y: U32, z: U32) -> U32:
  U32.xor(U32.and(x, y), U32.and(U32.not(x), z))

def maj(+x: U32, +y: U32, +z: U32) -> U32:
  U32.xor(U32.xor(U32.and(x, y), U32.and(x, z)), U32.and(y, z))

# A base-256 representation, most significant digit first, of fixed width.
def octets(width: Nat, +n: Nat) -> List<&2, U32>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, octets(p, Nat.div(n, 256n)),
        [U32.from_nat(Nat.mod(n, 256n))])

# 8*n = 256*(n/32) + 8*(n mod 32); avoids overflowing runtime Nat.
def length_field(+n: Nat) -> List<&2, U32>:
  List.append(&2, U32, octets(7n, Nat.div(n, 32n)),
    [U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n)])

# FIPS padding: a remainder of 0..55 leaves room in this block;
# a remainder of 56..63 needs another block. No modular shortcut is used.
def zero_count_if(r: Nat, fits: Bool) -> Nat:
  match fits:
    case True{}:
      Nat.sub(55n, r)
    case False{}:
      Nat.sub(119n, r)

def zero_count(+r: Nat) -> Nat:
  zero_count_if(r, Nat.is_le(r, 55n))

def padding_suffix(+n: Nat) -> List<&2, U32>:
  128 <> List.append(&2, U32,
    List.replicate(U32, zero_count(Nat.mod(n, 64n)), 0), length_field(n))

def pad(+bytes: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, bytes, padding_suffix(List.length(&2, U32, bytes)))

def decode(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.or(U32.shln(U32.and(a, 255), 24n),
    U32.shln(U32.and(b, 255), 16n)), U32.shln(U32.and(c, 255), 8n)), U32.and(d, 255))

def words(bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case a <> b <> c <> d <> rest:
      decode(a, b, c, d) <> words(rest)
    case _:
      Nil{}

# In reverse history, index j denotes W[t-1-j]. Only valid indices are
# reached for the actual 16-word input blocks; default zero makes nth total.
def nth(history: List<&2, U32>, index: Nat) -> U32:
  match history index:
    case Nil{} _:
      0
    case w <> rest 0n:
      w
    case w <> rest 1n+p:
      nth(rest, p)

# The FIPS recurrence names prior words by lags 2, 7, 15 and 16.
def previous(history: List<&2, U32>, lag: Nat) -> U32:
  nth(history, Nat.sub(lag, 1n))

def recurrence(+history: List<&2, U32>) -> U32:
  (sigma1(previous(history, 2n)) + previous(history, 7n)
    + sigma0(previous(history, 15n)) + previous(history, 16n) : U32)

def extension(rounds: Nat, +history: List<&2, U32>) -> List<&2, U32>:
  match rounds:
    case 0n:
      Nil{}
    case 1n+p:
      +w = recurrence(history)
      w <> extension(p, w <> history)

# Standard SHA-256 instantiates extra=48, extending the initial 16 to 64.
def schedule(extra: Nat, +block: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, block, extension(extra, List.reverse(&2, U32, block)))

def schedules(ws: List<&2, U32>, +extra: Nat) -> List<&2, List<&2, U32>>:
  match ws:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> rest:
      schedule(extra, [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]) <> schedules(rest, extra)
    case _:
      Nil{}

def prepare(bytes: List<&2, U32>, extra: Nat) -> List<&2, List<&2, U32>>:
  schedules(words(pad(bytes)), extra)

def step(s: Types.State, k: U32, w: U32) -> Types.State:
  Types.H{+a, +b, +c, d, +e, +f, +g, h} = s
  +t1 = (h + sum1(e) + ch(e, f, g) + k + w : U32)
  t2 = (sum0(a) + maj(a, b, c) : U32)
  Types.H{(t1 + t2 : U32), a, b, c, (d + t1 : U32), e, f, g}

def rounds(ks: List<&2, U32>, ws: List<&2, U32>) -> Types.State -> Types.State:
  match ks ws:
    case Nil{} _:
      s => s
    case k <> kt Nil{}:
      s => s
    case k <> kt w <> wt:
      next = rounds(kt, wt)
      s => next(step(s, k, w))

def feedforward(x: Types.State, y: Types.State) -> Types.State:
  Types.H{a, b, c, d, e, f, g, h} = x
  Types.H{i, j, k, l, m, n, o, p} = y
  Types.H{(a + i : U32), (b + j : U32), (c + k : U32), (d + l : U32),
    (e + m : U32), (f + n : U32), (g + o : U32), (h + p : U32)}

def compress(ws: List<&2, U32>, ks: List<&2, U32>, +s: Types.State) -> Types.State:
  feedforward(s, rounds(ks, ws)(s))

def blocks(prepared: List<&2, List<&2, U32>>, +ks: List<&2, U32>) -> Types.State -> Types.State:
  match prepared:
    case Nil{}:
      s => s
    case block <> rest:
      next = blocks(rest, ks)
      s => next(compress(block, ks, s))

def digest(s: Types.State) -> List<&2, U32>:
  Types.H{a, b, c, d, e, f, g, h} = s
  [a, b, c, d, e, f, g, h]

def hash(bytes: List<&2, U32>, extra: Nat, ks: List<&2, U32>) -> List<&2, U32>:
  digest(blocks(prepare(bytes, extra), ks)(initial()))

# FIPS 180-4 section 4.2.2, transcribed separately from the implementation.
def constants() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573,
   961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628,
   770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877,
   958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298]

def sha256(bytes: List<&2, U32>) -> List<&2, U32>:
  hash(bytes, 48n, constants())

# FIPS digest serialization: most significant octet of each word first.
def word_octets(+w: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(w, 24n), 255),
   U32.and(U32.shrn(w, 16n), 255),
   U32.and(U32.shrn(w, 8n), 255), U32.and(w, 255)]

def digest_octets(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> tail:
      List.append(&2, U32, word_octets(w), digest_octets(tail))

def sha256_bytes(bytes: List<&2, U32>) -> List<&2, U32>:
  digest_octets(sha256(bytes))
