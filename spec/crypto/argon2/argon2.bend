import Base
import ../../lib/common.bend as C
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../blake/blake2b.bend as B
import ./blamka.bend as G

# Argon2id, version 0x13 (RFC 9106), as an executable specification.
#
# Bytes are U32 values below 256, byte strings lists of them. The memory is
# a list of m' blocks (spec/crypto/argon2/blamka.bend's 128-lane blocks),
# B[i][j] being element i * q + j; indices are natural numbers and the
# reference-index arithmetic of section 3.4.1.2 is done on Nat. BLAKE2b is
# the RFC 7693 specification of spec/crypto/blake/blake2b.bend with the
# digest length in the parameter block; G is spec/crypto/argon2/blamka.bend's.
# The lanes are computed one after the other within a slice (every segment
# only reads blocks of finished segments of other lanes, so this is the
# RFC's parallel schedule, sequentially, as in the reference implementation).
#
# It shares nothing with src/crypto/argon2 but the record types of a lane, a
# state and a block.

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# ---------------------------------------------------------------- bytes

# LE32(n): the four little-endian bytes of n < 2^32.
def le32(+n: Nat) -> List<&2, U32>:
  [U32.from_nat(Nat.mod(n, 256n)), U32.from_nat(Nat.mod(Nat.div(n, 256n), 256n)), U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)), U32.from_nat(Nat.div(n, 16777216n))]

# The little-endian word of four bytes.
def word(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

# Bytes as little-endian words, the last one zero-padded.
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

def le(+w: U32) -> List<&2, U32>:
  [U32.and(w, 255), U32.and(U32.shrn(w, 8n), 255), U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)]

def lane_bytes(l: T.Lane) -> List<&2, U32>:
  match l:
    case T.W{lo, hi}:
      List.append(&2, U32, le(lo), le(hi))

# ---------------------------------------------------------------- BLAKE2b with digest length nn

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

def depth_go(fuel: Nat, +n: Nat, +d: Nat, done: Bool) -> Nat:
  match fuel done:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+f False{}:
      depth_go(f, n, 1n+d, Nat.is_le(n, pw(1n+d)))

# The bytes packed in the BLAKE2b specification's input array.
def pack(bs: List<&2, U32>) -> Array<U32>:
  +ws = words(bs)
  +n = List.length(&2, U32, ws)
  fill(ws, 0, Array.new(U32, depth_go(32n, n, 0n, Nat.is_le(n, 1n)), 0))

# RFC 7693 section 2.5: h[0] ^= 0x01010000 ^ (kk << 8) ^ nn with kk = 0.
def initial(+nn: U32) -> T.Chain:
  T.H{B.xor(B.iv(0n), T.W{U32.or(16842752, nn), 0}), B.iv(1n), B.iv(2n), B.iv(3n), B.iv(4n), B.iv(5n), B.iv(6n), B.iv(7n)}

def chain_bytes(h: T.Chain) -> List<&2, U32>:
  match h:
    case T.H{h0, h1, h2, h3, h4, h5, h6, h7}:
      List.concat(&2, U32, [lane_bytes(h0), lane_bytes(h1), lane_bytes(h2), lane_bytes(h3), lane_bytes(h4), lane_bytes(h5), lane_bytes(h6), lane_bytes(h7)])

# H^nn(bs): BLAKE2b with an nn-byte digest, 1 <= nn <= 64: the first nn bytes
# of h after the dd = max(1, ceil(ll / 128)) blocks.
def hash(+nn: Nat, +bs: List<&2, U32>) -> List<&2, U32>:
  +ll = List.length(&2, U32, bs)
  +n = Nat.div(Nat.sub(ll, 1n), 128n)
  List.take(&2, U32, chain_bytes(B.blocks(n, 0, Nat.sub(ll, Nat.mul(n, 128n)), T.C{0, 0, 0, 0}, (pack(bs), initial(U32.from_nat(nn))))), nn)

# ---------------------------------------------------------------- H0 and H' (sections 3.2 and 3.3)

# r = ceil(T / 32) - 2; V1 = H^64(LE32(T) || A), V_{i+1} = H^64(V_i),
# V_{r+1} = H^{T - 32r}(V_r); the output is W1 || .. || Wr || V_{r+1}, Wi
# the first 32 bytes of Vi.
# (V_i is a 64-byte digest, never empty; it is inspected first so that proofs
# keep the chain of hashes folded.)
def hp_go(n: Nat, v: List<&2, U32>, +last: Nat) -> List<&2, U32>:
  match n v:
    case _ Nil{}:
      Nil{}
    case 0n +x <> +r:
      cat(List.take(&2, U32, x <> r, 32n), hash(last, x <> r))
    case 1n+p +x <> +r:
      cat(List.take(&2, U32, x <> r, 32n), hp_go(p, hash(64n, x <> r), last))

def hp_pick(+tl: Nat, +x: List<&2, U32>, short: Bool) -> List<&2, U32>:
  match short:
    case True{}:
      hash(tl, x)
    case False{}:
      +r = Nat.sub(Nat.div(Nat.add(tl, 31n), 32n), 2n)
      hp_go(Nat.sub(r, 1n), hash(64n, x), Nat.sub(tl, Nat.mul(32n, r)))

# H'^T(a) = H^T(LE32(T) || a) if T <= 64, else as hp_go.
def hprime(+tl: Nat, a: List<&2, U32>) -> List<&2, U32>:
  hp_pick(tl, cat(le32(tl), a), Nat.is_le(tl, 64n))

# H0 = H^64(LE32(p) || LE32(T) || LE32(m) || LE32(t) || LE32(v) || LE32(y) ||
# LE32(|P|) || P || LE32(|S|) || S || LE32(|K|) || K || LE32(|X|) || X), with
# v = 0x13 and y = 2 (Argon2id).
def h0(+p: Nat, +tl: Nat, +m: Nat, +t: Nat, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>) -> List<&2, U32>:
  hash(64n, cat(le32(p), cat(le32(tl), cat(le32(m), cat(le32(t), cat(le32(19n), cat(le32(2n), cat(le32(len(pw)), cat(pw, cat(le32(len(salt)), cat(salt, cat(le32(len(key)), cat(key, cat(le32(len(ad)), ad))))))))))))))

# ---------------------------------------------------------------- blocks and bytes

# 32 words (a row) as sixteen lanes, and the words left.
def row_of(ws: List<&2, U32>) -> T.State & List<&2, U32>:
  match ws:
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> w29 <> w30 <> w31 <> rest:
      (T.V{T.W{w0, w1}, T.W{w2, w3}, T.W{w4, w5}, T.W{w6, w7}, T.W{w8, w9}, T.W{w10, w11}, T.W{w12, w13}, T.W{w14, w15}, T.W{w16, w17}, T.W{w18, w19}, T.W{w20, w21}, T.W{w22, w23}, T.W{w24, w25}, T.W{w26, w27}, T.W{w28, w29}, T.W{w30, w31}}, rest)
    case _:
      (G.zero_state(), Nil{})

def rows_of7(r0: T.State, r1: T.State, r2: T.State, r3: T.State, r4: T.State, r5: T.State, r6: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r7, ws) = p
  A.B{r0, r1, r2, r3, r4, r5, r6, r7}

def rows_of6(r0: T.State, r1: T.State, r2: T.State, r3: T.State, r4: T.State, r5: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r6, ws) = p
  rows_of7(r0, r1, r2, r3, r4, r5, r6, row_of(ws))

def rows_of5(r0: T.State, r1: T.State, r2: T.State, r3: T.State, r4: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r5, ws) = p
  rows_of6(r0, r1, r2, r3, r4, r5, row_of(ws))

def rows_of4(r0: T.State, r1: T.State, r2: T.State, r3: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r4, ws) = p
  rows_of5(r0, r1, r2, r3, r4, row_of(ws))

def rows_of3(r0: T.State, r1: T.State, r2: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r3, ws) = p
  rows_of4(r0, r1, r2, r3, row_of(ws))

def rows_of2(r0: T.State, r1: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r2, ws) = p
  rows_of3(r0, r1, r2, row_of(ws))

def rows_of1(r0: T.State, p: T.State & List<&2, U32>) -> A.Block:
  (r1, ws) = p
  rows_of2(r0, r1, row_of(ws))

def rows_of0(p: T.State & List<&2, U32>) -> A.Block:
  (r0, ws) = p
  rows_of1(r0, row_of(ws))

# The block of 1024 bytes: lane n is the little-endian 64-bit word of bytes 8n .. 8n + 7.
def block_of(bs: List<&2, U32>) -> A.Block:
  rows_of0(row_of(words(bs)))

def state_bytes(v: T.State) -> List<&2, U32>:
  match v:
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      List.concat(&2, U32, [lane_bytes(x0), lane_bytes(x1), lane_bytes(x2), lane_bytes(x3), lane_bytes(x4), lane_bytes(x5), lane_bytes(x6), lane_bytes(x7), lane_bytes(x8), lane_bytes(x9), lane_bytes(x10), lane_bytes(x11), lane_bytes(x12), lane_bytes(x13), lane_bytes(x14), lane_bytes(x15)])

# The 1024 bytes of a block.
def block_bytes(b: A.Block) -> List<&2, U32>:
  match b:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7}:
      List.concat(&2, U32, [state_bytes(r0), state_bytes(r1), state_bytes(r2), state_bytes(r3), state_bytes(r4), state_bytes(r5), state_bytes(r6), state_bytes(r7)])

# ---------------------------------------------------------------- memory

# B[i][j] of the memory is element i * q + j; a block out of range reads as zero.
def get(mem: List<&2, A.Block>, +b: Nat) -> A.Block:
  Maybe.default(&2, A.Block, C.nth(A.Block, mem, b), G.zero())

def set(mem: List<&2, A.Block>, +b: Nat, v: A.Block) -> List<&2, A.Block>:
  C.update(A.Block, mem, b, v)

# ---------------------------------------------------------------- indexing (section 3.4)

def small(+x: Nat) -> T.Lane:
  T.W{U32.from_nat(x), 0}

# Z = (r, l, s, m', t, y, i) as the first seven 64-bit lanes of a zero block.
def input_of(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  G.put_lanes([0n, 1n, 2n, 3n, 4n, 5n, 6n], [small(r), small(l), small(s), small(mm), small(t), small(2n), small(ctr)], G.zero())

# (r is inspected first, so that proofs keep an input block with a symbolic
# pass number folded instead of evaluating G on it.)
def input_block(r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  match r:
    case 0n:
      input_of(0n, l, s, mm, t, ctr)
    case 1n+x:
      input_of(1n+x, l, s, mm, t, ctr)

# The address block with counter ctr: G(ZERO, G(ZERO, Z)).
def addresses(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  G.G(G.zero(), G.G(G.zero(), input_block(r, l, s, mm, t, ctr)))

# In a data-independent segment a new address block is computed for the
# segment's first position and at every multiple of 128, with counter
# idx / 128 + 1 (the i-th address block has counter i).
def regen(need: Bool, addr: A.Block, +r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +idx: Nat) -> A.Block:
  match need:
    case True{}:
      addresses(r, l, s, mm, t, Nat.add(Nat.div(idx, 128n), 1n))
    case False{}:
      addr

# |W|: in the first pass, the blocks of finished segments of the lane (all
# previous blocks of the segment too, when the reference lane is the current
# one); in later passes the last three segments of the lane, plus the current
# segment's previous blocks for the same lane; never the block just before
# the current one ("minus one" when the current index is the first of its
# segment and the lane is another one).
def area_base(r0: Bool, +s: Nat, +sl: Nat, +q: Nat) -> Nat:
  match r0:
    case True{}:
      Nat.mul(s, sl)
    case False{}:
      Nat.sub(q, sl)

def area_other(+base: Nat, zero: Bool) -> Nat:
  match zero:
    case True{}:
      Nat.sub(base, 1n)
    case False{}:
      base

def area(+base: Nat, +idx: Nat, same: Bool) -> Nat:
  match same:
    case True{}:
      Nat.sub(Nat.add(base, idx), 1n)
    case False{}:
      area_other(base, Nat.is_eq(idx, 0n))

# x = J1^2 / 2^32; y = (|W| * x) / 2^32; zz = |W| - 1 - y.
def rel(+w: Nat, +j1: U32) -> Nat:
  +x = C.high(32n, Nat.mul(U32.to_nat(j1), U32.to_nat(j1)))
  Nat.sub(Nat.sub(w, 1n), C.high(32n, Nat.mul(w, x)))

def start_last(+s: Nat, +sl: Nat, last: Bool) -> Nat:
  match last:
    case True{}:
      0n
    case False{}:
      Nat.mul(Nat.add(s, 1n), sl)

# The reference area starts at 0 in the first pass, else at the next segment.
def start(r0: Bool, +s: Nat, +sl: Nat) -> Nat:
  match r0:
    case True{}:
      0n
    case False{}:
      start_last(s, sl, Nat.is_eq(s, 3n))

# l = J2 mod p, except in the first slice of the first pass (the current lane).
def ref_lane(forced: Bool, +l: Nat, +j2: U32, +p: Nat) -> Nat:
  match forced:
    case True{}:
      l
    case False{}:
      Nat.mod(U32.to_nat(j2), p)

# The previous block: B[l][j - 1], or B[l][q - 1] for j = 0.
def prev_index(+l: Nat, +q: Nat, +j: Nat, first: Bool) -> Nat:
  match first:
    case True{}:
      Nat.add(Nat.mul(l, q), Nat.sub(q, 1n))
    case False{}:
      Nat.sub(Nat.add(Nat.mul(l, q), j), 1n)

# J1 || J2: the address block's lane idx mod 128 (data-independent), or the
# first lane of the previous block (data-dependent).
def pick(indep: Bool, +addr: A.Block, +idx: Nat, +prev: A.Block) -> T.Lane:
  match indep:
    case True{}:
      G.lane(addr, Nat.mod(idx, 128n))
    case False{}:
      G.lane(prev, 0n)

def lo(x: T.Lane) -> U32:
  match x:
    case T.W{l, h}:
      l

def hi(x: T.Lane) -> U32:
  match x:
    case T.W{l, h}:
      h

# ---------------------------------------------------------------- filling (section 3.2, steps 5 and 6)

# B[l][j] = G(B[l][j-1], B[l'][z']) in the first pass; XORed into the old
# B[l][j] in later passes (version 0x13).
def store(r0: Bool, +cur: Nat, +prev: A.Block, +refb: A.Block, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  match r0:
    case True{}:
      set(mem, cur, G.G(prev, refb))
    case False{}:
      set(mem, cur, G.xor(G.G(prev, refb), get(mem, cur)))

def step(+r: Nat, +l: Nat, +s: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +cur: Nat, +indep: Bool, +addr: A.Block, +prev: A.Block, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  +r0 = Nat.is_eq(r, 0n)
  +pr = pick(indep, addr, idx, prev)
  +rl = ref_lane(Bool.and(r0, Nat.is_eq(s, 0n)), l, hi(pr), p)
  +w = area(area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l))
  +ri = Nat.mod(Nat.add(start(r0, s, sl), rel(w, lo(pr))), q)
  store(r0, cur, prev, get(mem, Nat.add(Nat.mul(rl, q), ri)), mem)

# Positions idx .. idx + n - 1 of segment (r, s) of lane l.
def seg_go(n: Nat, +idx: Nat, first: Bool, addr: A.Block, +mem: List<&2, A.Block>, +r: Nat, +l: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +indep: Bool) -> List<&2, A.Block>:
  match n:
    case 0n:
      mem
    case 1n+rest:
      +addr2 = regen(Bool.and(indep, Bool.or(first, Nat.is_eq(Nat.mod(idx, 128n), 0n))), addr, r, l, s, mm, t, idx)
      +j = Nat.add(Nat.mul(s, sl), idx)
      +cur = Nat.add(Nat.mul(l, q), j)
      +prev = get(mem, prev_index(l, q, j, Nat.is_eq(j, 0n)))
      seg_go(rest, Nat.add(idx, 1n), False{}, addr2, step(r, l, s, idx, p, q, sl, cur, indep, addr2, prev, mem), r, l, s, p, q, sl, mm, t, indep)

def start_index(first: Bool) -> Nat:
  match first:
    case True{}:
      2n
    case False{}:
      0n

# Segment s of lane l in pass r; data-independent addressing (Argon2i) in the
# first two slices of the first pass, data-dependent (Argon2d) otherwise.
def segment(+r: Nat, +s: Nat, +l: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  +r0 = Nat.is_eq(r, 0n)
  +st = start_index(Bool.and(r0, Nat.is_eq(s, 0n)))
  seg_go(Nat.sub(sl, st), st, True{}, G.zero(), mem, r, l, s, p, q, sl, mm, t, Bool.and(r0, Nat.is_lt(s, 2n)))

def lanes_go(n: Nat, +l: Nat, +r: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  match n:
    case 0n:
      mem
    case 1n+rest:
      lanes_go(rest, Nat.add(l, 1n), r, s, p, q, sl, mm, t, segment(r, s, l, p, q, sl, mm, t, mem))

def slices_go(n: Nat, +s: Nat, +r: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  match n:
    case 0n:
      mem
    case 1n+rest:
      slices_go(rest, Nat.add(s, 1n), r, p, q, sl, mm, t, lanes_go(p, 0n, r, s, p, q, sl, mm, t, mem))

def passes_go(n: Nat, +r: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  match n:
    case 0n:
      mem
    case 1n+rest:
      passes_go(rest, Nat.add(r, 1n), p, q, sl, mm, t, slices_go(4n, 0n, r, p, q, sl, mm, t, mem))

# B[l][0] = H'^1024(H0 || LE32(0) || LE32(l)), B[l][1] = H'^1024(H0 || LE32(1) || LE32(l)).
def init_go(n: Nat, +l: Nat, +q: Nat, +hh: List<&2, U32>, +mem: List<&2, A.Block>) -> List<&2, A.Block>:
  match n:
    case 0n:
      mem
    case 1n+rest:
      +b0 = block_of(hprime(1024n, cat(hh, cat(le32(0n), le32(l)))))
      +b1 = block_of(hprime(1024n, cat(hh, cat(le32(1n), le32(l)))))
      init_go(rest, Nat.add(l, 1n), q, hh, set(set(mem, Nat.mul(l, q), b0), Nat.add(Nat.mul(l, q), 1n), b1))

# C = B[0][q-1] XOR B[1][q-1] XOR .. XOR B[p-1][q-1]: b is B[l][q-1], n more
# lanes follow.
def final_go(n: Nat, +l: Nat, +q: Nat, c: A.Block, b: A.Block, +mem: List<&2, A.Block>) -> A.Block:
  match n:
    case 0n:
      G.xor(c, b)
    case 1n+rest:
      final_go(rest, Nat.add(l, 1n), q, G.xor(c, b), get(mem, Nat.add(Nat.mul(Nat.add(l, 1n), q), Nat.sub(q, 1n))), mem)

# ---------------------------------------------------------------- Argon2id

# RFC 9106 section 3.1: 1 <= p <= 2^24 - 1, 4 <= T <= 2^32 - 1,
# 8p <= m <= 2^32 - 1, 1 <= t <= 2^32 - 1, 8 <= |S| <= 2^32 - 1 and |P|, |K|,
# |X| <= 2^32 - 1.
def valid(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Bool:
  Bool.and(Bool.and(Bool.and(Nat.is_le(1n, p), Nat.is_le(p, 16777215n)), Bool.and(Nat.is_le(4n, tl), Nat.is_le(tl, 4294967295n))),
    Bool.and(Bool.and(Bool.and(Nat.is_le(Nat.mul(8n, p), m), Nat.is_le(m, 4294967295n)), Bool.and(Nat.is_le(1n, t), Nat.is_le(t, 4294967295n))),
      Bool.and(Bool.and(Nat.is_le(8n, len(salt)), Nat.is_le(len(salt), 4294967295n)), Bool.and(Nat.is_le(len(pw), 4294967295n), Bool.and(Nat.is_le(len(key), 4294967295n), Nat.is_le(len(ad), 4294967295n))))))

# The tag: m' = 4p floor(m / 4p) blocks, q = m' / p columns, segments of q / 4.
def run(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> List<&2, U32>:
  +mm = Nat.mul(Nat.mul(4n, p), Nat.div(m, Nat.mul(4n, p)))
  +q = Nat.div(mm, p)
  +sl = Nat.div(q, 4n)
  +hh = h0(p, tl, m, t, pw, salt, key, ad)
  +mem = passes_go(t, 0n, p, q, sl, mm, t, init_go(p, 0n, q, hh, C.replicate(A.Block, mm, G.zero())))
  hprime(tl, block_bytes(final_go(Nat.sub(p, 1n), 0n, q, G.zero(), get(mem, Nat.sub(q, 1n)), mem)))

def checked(ok: Bool, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{run(pw, salt, key, ad, t, m, p, tl)}
    case False{}:
      None{}

# Argon2id(P, S, K, X; t passes, m KiB of memory, p lanes, T tag bytes), or
# None when a parameter is out of range.
def argon2id(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Maybe<&2, List<&2, U32>>:
  checked(valid(pw, salt, key, ad, t, m, p, tl), pw, salt, key, ad, t, m, p, tl)
