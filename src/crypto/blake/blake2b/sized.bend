import Base
import ./types.bend as T
import ./blake2b.bend as B

# BLAKE2b with a digest length nn in 1..64 bytes (RFC 7693 section 2.5: the
# parameter block's first byte is nn), unkeyed, over a list of bytes (U32
# values below 256). Argon2 (RFC 9106) uses it for H^T and H'. The blocks are
# compressed by the proved BLAKE2b-512 implementation of blake2b.bend; only
# the initial chaining value and the digest length differ.

# Four little-endian bytes as one word.
def word(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

# The bytes packed four per word, the last word zero-padded.
def words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case b0 <> Nil{}:
      [word(b0, 0, 0, 0)]
    case b0 <> b1 <> Nil{}:
      [word(b0, b1, 0, 0)]
    case b0 <> b1 <> b2 <> Nil{}:
      [word(b0, b1, b2, 0)]
    case b0 <> b1 <> b2 <> b3 <> rest:
      word(b0, b1, b2, b3) <> words(rest)

def fill(ws: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case w <> rest:
      fill(rest, U32.inc(i), Array.set(U32, a, i, w))

def pw(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pw(p))

# The smallest d >= k with 2^d >= n.
def depth_go(fuel: Nat, +n: Nat, +d: Nat, done: Bool) -> Nat:
  match fuel done:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+f False{}:
      depth_go(f, n, 1n+d, Nat.is_le(n, pw(1n+d)))

def depth(+n: Nat) -> Nat:
  depth_go(32n, n, 0n, Nat.is_le(n, 1n))

# The packed array of the bytes.
def pack(bs: List<&2, U32>) -> Array<U32>:
  +ws = words(bs)
  fill(ws, 0, Array.new(U32, depth(List.length(&2, U32, ws)), 0))

# h[0] ^= 0x01010000 ^ nn: the parameter block of an unkeyed hash with nn bytes.
def initial(+nn: U32) -> T.Chain:
  T.H{T.W{U32.xor(4089235720, U32.or(16842752, nn)), 1779033703}, T.W{2227873595, 3144134277}, T.W{4271175723, 1013904242}, T.W{1595750129, 2773480762}, T.W{2917565137, 1359893119}, T.W{725511199, 2600822924}, T.W{4215389547, 528734635}, T.W{327033209, 1541459225}}

def le(+w: U32) -> List<&2, U32>:
  [U32.and(w, 255), U32.and(U32.shrn(w, 8n), 255), U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)]

def lane_bytes(l: T.Lane) -> List<&2, U32>:
  match l:
    case T.W{lo, hi}:
      List.append(&2, U32, le(lo), le(hi))

# The 64 little-endian bytes of the chaining value.
def chain_bytes(h: T.Chain) -> List<&2, U32>:
  match h:
    case T.H{h0, h1, h2, h3, h4, h5, h6, h7}:
      List.concat(&2, U32, [lane_bytes(h0), lane_bytes(h1), lane_bytes(h2), lane_bytes(h3), lane_bytes(h4), lane_bytes(h5), lane_bytes(h6), lane_bytes(h7)])

# The chaining value after every block: dd - 1 = (ll - 1) div 128 full blocks,
# then the last one (RFC 7693 section 3.3).
def chain(+nn: Nat, a: Array<U32>, +ll: Nat) -> T.Chain:
  +n = Nat.div(Nat.sub(ll, 1n), 128n)
  B.blocks(n, 0, Nat.sub(ll, Nat.mul(n, 128n)), T.C{0, 0, 0, 0}, (a, initial(U32.from_nat(nn))))

# BLAKE2b with an nn-byte digest (1 <= nn <= 64) of the bytes.
def hash(+nn: Nat, +bs: List<&2, U32>) -> List<&2, U32>:
  +ll = List.length(&2, U32, bs)
  List.take(&2, U32, chain_bytes(chain(nn, pack(bs), ll)), nn)
