import Base
import ../../lib/common.bend as C
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../blake/blake2b.bend as B

# The Argon2 compression function G (RFC 9106 sections 3.5 and 3.6), as an
# executable specification. It shares with the implementation only the
# record types (a 64-bit lane T.W{lo, hi}, a 16-lane state T.V, a 128-lane
# block A.B of eight rows), and takes the 64-bit addition, XOR and rotation
# from the RFC 7693 BLAKE2b specification (spec/crypto/blake/blake2b.bend).
# Lanes of a block are numbered 0..127, lane n being row n / 16, position
# n mod 16; the 1024-byte block is the 128 lanes in order, little-endian.

# ---------------------------------------------------------------- GB

# The lane of n mod 2^64 (U32.from_nat keeps the low 32 bits).
def lane_of(+n: Nat) -> T.Lane:
  T.W{U32.from_nat(C.low(32n, n)), U32.from_nat(C.high(32n, n))}

# fBlaMka(x, y) = x + y + 2 * trunc(x) * trunc(y), modulo 2^64, where
# trunc(x) * trunc(y) is the 64-bit product of the low 32 bits of x and y.
def fBlaMka(x: T.Lane, y: T.Lane) -> T.Lane:
  match x y:
    case T.W{+xl, +xh} T.W{+yl, +yh}:
      +p = lane_of(Nat.mul(U32.to_nat(xl), U32.to_nat(yl)))
      B.add(B.add(T.W{xl, xh}, T.W{yl, yh}), B.add(p, p))

# GB(a, b, c, d) (RFC 9106 section 3.6).
def GB(+a: T.Lane, +b: T.Lane, +c: T.Lane, +d: T.Lane) -> T.Quad:
  +a1 = fBlaMka(a, b)
  +d1 = B.rotr(B.xor(d, a1), 32n)
  +c1 = fBlaMka(c, d1)
  +b1 = B.rotr(B.xor(b, c1), 24n)
  +a2 = fBlaMka(a1, b1)
  +d2 = B.rotr(B.xor(d1, a2), 16n)
  +c2 = fBlaMka(c1, d2)
  +b2 = B.rotr(B.xor(b1, c2), 63n)
  T.Q{a2, b2, c2, d2}

# ---------------------------------------------------------------- P

def apply(v: T.State, +a: Nat, +b: Nat, +c: Nat, +d: Nat, q: T.Quad) -> T.State:
  match q:
    case T.Q{qa, qb, qc, qd}:
      B.put(B.put(B.put(B.put(v, a, qa), b, qb), c, qc), d, qd)

# (v_a, v_b, v_c, v_d) <- GB(v_a, v_b, v_c, v_d)
def GBw(+w: T.State, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> T.State:
  apply(w, a, b, c, d, GB(B.at(w, a), B.at(w, b), B.at(w, c), B.at(w, d)))

def GBi(v: T.State, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> T.State:
  match v:
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      GBw(T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, a, b, c, d)

# The permutation P on sixteen lanes v0..v15: GB on the columns (0, 4, 8, 12),
# (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), then on the diagonals
# (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14).
def P(v: T.State) -> T.State:
  v = GBi(v, 0n, 4n, 8n, 12n)
  v = GBi(v, 1n, 5n, 9n, 13n)
  v = GBi(v, 2n, 6n, 10n, 14n)
  v = GBi(v, 3n, 7n, 11n, 15n)
  v = GBi(v, 0n, 5n, 10n, 15n)
  v = GBi(v, 1n, 6n, 11n, 12n)
  v = GBi(v, 2n, 7n, 8n, 13n)
  GBi(v, 3n, 4n, 9n, 14n)

# ---------------------------------------------------------------- blocks

def row(b: A.Block, i: Nat) -> T.State:
  match b i:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 0n:
      r0
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 1n:
      r1
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 2n:
      r2
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 3n:
      r3
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 4n:
      r4
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 5n:
      r5
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 6n:
      r6
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} _:
      r7

def put_row(b: A.Block, i: Nat, s: T.State) -> A.Block:
  match b i:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 0n:
      A.B{s, r1, r2, r3, r4, r5, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 1n:
      A.B{r0, s, r2, r3, r4, r5, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 2n:
      A.B{r0, r1, s, r3, r4, r5, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 3n:
      A.B{r0, r1, r2, s, r4, r5, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 4n:
      A.B{r0, r1, r2, r3, s, r5, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 5n:
      A.B{r0, r1, r2, r3, r4, s, r6, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 6n:
      A.B{r0, r1, r2, r3, r4, r5, s, r7}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} _:
      A.B{r0, r1, r2, r3, r4, r5, r6, s}

# Lane n of a block, and the block with lane n replaced.
def lane(+b: A.Block, +n: Nat) -> T.Lane:
  B.at(row(b, Nat.div(n, 16n)), Nat.mod(n, 16n))

def put_lane(+b: A.Block, +n: Nat, x: T.Lane) -> A.Block:
  +i = Nat.div(n, 16n)
  put_row(b, i, B.put(row(b, i), Nat.mod(n, 16n), x))

def ix(xs: List<&2, Nat>, n: Nat) -> Nat:
  B.nth(Nat, xs, n, 0n)

# The sixteen lanes at the given lane numbers, as a state.
def gather(+b: A.Block, +idx: List<&2, Nat>) -> T.State:
  T.V{lane(b, ix(idx, 0n)), lane(b, ix(idx, 1n)), lane(b, ix(idx, 2n)), lane(b, ix(idx, 3n)), lane(b, ix(idx, 4n)), lane(b, ix(idx, 5n)), lane(b, ix(idx, 6n)), lane(b, ix(idx, 7n)), lane(b, ix(idx, 8n)), lane(b, ix(idx, 9n)), lane(b, ix(idx, 10n)), lane(b, ix(idx, 11n)), lane(b, ix(idx, 12n)), lane(b, ix(idx, 13n)), lane(b, ix(idx, 14n)), lane(b, ix(idx, 15n))}

def put_lanes(idx: List<&2, Nat>, xs: List<&2, T.Lane>, b: A.Block) -> A.Block:
  match idx xs:
    case n <> ns x <> rest:
      put_lanes(ns, rest, put_lane(b, n, x))
    case _ _:
      b

# The block with the state's sixteen lanes stored at the given lane numbers.
def scatter(b: A.Block, idx: List<&2, Nat>, s: T.State) -> A.Block:
  match s:
    case T.V{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      put_lanes(idx, [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15], b)

# first, first + step, .., n terms.
def seq(n: Nat, +first: Nat, +step: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      first <> seq(k, Nat.add(first, step), step)

# Row i: lanes 16i, 16i + 1, .., 16i + 15.
def row_idx(+i: Nat) -> List<&2, Nat>:
  seq(16n, Nat.mul(16n, i), 1n)

# Column i: the 16-byte registers i, i + 8, .., i + 56, that is lanes
# 2i, 2i + 1, 2i + 16, 2i + 17, .., 2i + 112, 2i + 113.
def col_pairs(n: Nat, +first: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      first <> Nat.add(first, 1n) <> col_pairs(k, Nat.add(first, 16n))

def col_idx(+i: Nat) -> List<&2, Nat>:
  col_pairs(8n, Nat.mul(2n, i))

# P applied, independently, to the lanes of each index list of b.
def perms(+b: A.Block, idxs: List<&2, List<&2, Nat>>) -> List<&2, T.State>:
  match idxs:
    case Nil{}:
      Nil{}
    case i <> rest:
      P(gather(b, i)) <> perms(b, rest)

def scatter_all(idxs: List<&2, List<&2, Nat>>, ss: List<&2, T.State>, b: A.Block) -> A.Block:
  match idxs ss:
    case i <> ix s <> rest:
      scatter_all(ix, rest, scatter(b, i, s))
    case _ _:
      b

def permute(+b: A.Block, +idxs: List<&2, List<&2, Nat>>) -> A.Block:
  scatter_all(idxs, perms(b, idxs), b)

def rows_all() -> List<&2, List<&2, Nat>>:
  [row_idx(0n), row_idx(1n), row_idx(2n), row_idx(3n), row_idx(4n), row_idx(5n), row_idx(6n), row_idx(7n)]

def cols_all() -> List<&2, List<&2, Nat>>:
  [col_idx(0n), col_idx(1n), col_idx(2n), col_idx(3n), col_idx(4n), col_idx(5n), col_idx(6n), col_idx(7n)]

# (Q0, .., Q7) <- P(R0, .., R7), .., (Q56, .., Q63) <- P(R56, .., R63): P on
# each row of eight 16-byte registers.
def rows(b: A.Block) -> A.Block:
  match b:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7}:
      permute(A.B{r0, r1, r2, r3, r4, r5, r6, r7}, rows_all())

# (Z0, Z8, .., Z56) <- P(Q0, Q8, .., Q56), .., (Z7, .., Z63) <- P(Q7, .., Q63):
# P on each column.
def cols(b: A.Block) -> A.Block:
  match b:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7}:
      permute(A.B{r0, r1, r2, r3, r4, r5, r6, r7}, cols_all())

def xor_state(s: T.State, t: T.State) -> T.State:
  match s t:
    case T.V{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15} T.V{t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15}:
      T.V{B.xor(s0, t0), B.xor(s1, t1), B.xor(s2, t2), B.xor(s3, t3), B.xor(s4, t4), B.xor(s5, t5), B.xor(s6, t6), B.xor(s7, t7), B.xor(s8, t8), B.xor(s9, t9), B.xor(s10, t10), B.xor(s11, t11), B.xor(s12, t12), B.xor(s13, t13), B.xor(s14, t14), B.xor(s15, t15)}

# X XOR Y, lane by lane.
def xor(x: A.Block, y: A.Block) -> A.Block:
  match x y:
    case A.B{x0, x1, x2, x3, x4, x5, x6, x7} A.B{y0, y1, y2, y3, y4, y5, y6, y7}:
      A.B{xor_state(x0, y0), xor_state(x1, y1), xor_state(x2, y2), xor_state(x3, y3), xor_state(x4, y4), xor_state(x5, y5), xor_state(x6, y6), xor_state(x7, y7)}

# G(X, Y) = Z XOR R, where R = X XOR Y, Q = P on the rows of R and Z = P on
# the columns of Q (RFC 9106 section 3.5).
def G(x: A.Block, y: A.Block) -> A.Block:
  +r = xor(x, y)
  xor(cols(rows(r)), r)

def zero_state() -> T.State:
  T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}

# The all-zero block.
def zero() -> A.Block:
  A.B{zero_state(), zero_state(), zero_state(), zero_state(), zero_state(), zero_state(), zero_state(), zero_state()}
