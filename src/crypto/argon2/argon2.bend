import Base
import ../../math/w64.bend as X
import ../blake/blake2b/types.bend as T
import ../blake/blake2b/sized.bend as H
import ./types.bend as A
import ./blamka.bend as G
import ./sub.bend as SB
import ./memory.bend as M

# Argon2id, version 0x13 (RFC 9106). Bytes are U32 values below 256; every
# size is a Nat. The memory is the packed Array<U32> of memory.bend; the
# blocks are compressed by blamka.bend. The lanes are filled one after the
# other within a slice (a sequential schedule of the RFC's parallel one).

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# LE32(n) for n < 2^32.
def le32(+n: Nat) -> List<&2, U32>:
  [U32.from_nat(Nat.mod(n, 256n)), U32.from_nat(Nat.mod(Nat.div(n, 256n), 256n)), U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)), U32.from_nat(Nat.div(n, 16777216n))]

# ---------------------------------------------------------------- H0 and H'

# H' for T > 64 (RFC 9106 section 3.3): W1 || .. || Wr || V_{r+1}, where
# Wi is the first 32 bytes of Vi, V_{i+1} = H^64(Vi) and V_{r+1} = H^{T-32r}(Vr).
# (V_i is a 64-byte digest, never empty; it is inspected first so that proofs
# keep the chain of hashes folded.)
def hp_go(n: Nat, v: List<&2, U32>, +last: Nat) -> List<&2, U32>:
  match n v:
    case _ Nil{}:
      Nil{}
    case 0n +x <> +r:
      cat(List.take(&2, U32, x <> r, 32n), H.hash(last, x <> r))
    case 1n+p +x <> +r:
      cat(List.take(&2, U32, x <> r, 32n), hp_go(p, H.hash(64n, x <> r), last))

def hp_pick(+tl: Nat, +x: List<&2, U32>, short: Bool) -> List<&2, U32>:
  match short:
    case True{}:
      H.hash(tl, x)
    case False{}:
      +r = Nat.sub(Nat.div(Nat.add(tl, 31n), 32n), 2n)
      hp_go(Nat.sub(r, 1n), H.hash(64n, x), Nat.sub(tl, Nat.mul(32n, r)))

# H'^T(a): the variable-length hash, over LE32(T) || a.
def hprime(+tl: Nat, a: List<&2, U32>) -> List<&2, U32>:
  hp_pick(tl, cat(le32(tl), a), Nat.is_le(tl, 64n))

# H0 (RFC 9106 section 3.2, step 1), version 0x13 and type 2 (Argon2id).
def h0(+p: Nat, +tl: Nat, +m: Nat, +t: Nat, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>) -> List<&2, U32>:
  H.hash(64n, cat(le32(p), cat(le32(tl), cat(le32(m), cat(le32(t), cat(le32(19n), cat(le32(2n), cat(le32(len(pw)), cat(pw, cat(le32(len(salt)), cat(salt, cat(le32(len(key)), cat(key, cat(le32(len(ad)), ad))))))))))))))

# ---------------------------------------------------------------- blocks and bytes

# A block from its 1024 little-endian bytes.
def block_of(bs: List<&2, U32>) -> A.Block:
  SB.rows8(H.words(bs))

def state_bytes(v: T.State) -> List<&2, U32>:
  match v:
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      List.concat(&2, U32, [H.lane_bytes(x0), H.lane_bytes(x1), H.lane_bytes(x2), H.lane_bytes(x3), H.lane_bytes(x4), H.lane_bytes(x5), H.lane_bytes(x6), H.lane_bytes(x7), H.lane_bytes(x8), H.lane_bytes(x9), H.lane_bytes(x10), H.lane_bytes(x11), H.lane_bytes(x12), H.lane_bytes(x13), H.lane_bytes(x14), H.lane_bytes(x15)])

# The 1024 little-endian bytes of a block.
def block_bytes(b: A.Block) -> List<&2, U32>:
  match b:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7}:
      List.concat(&2, U32, [state_bytes(r0), state_bytes(r1), state_bytes(r2), state_bytes(r3), state_bytes(r4), state_bytes(r5), state_bytes(r6), state_bytes(r7)])

def row_at(b: A.Block, +i: Nat) -> T.State:
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

def at(v: T.State, +j: Nat) -> T.Lane:
  match v j:
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 0n:
      x0
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 1n:
      x1
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 2n:
      x2
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 3n:
      x3
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 4n:
      x4
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 5n:
      x5
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 6n:
      x6
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 7n:
      x7
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 8n:
      x8
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 9n:
      x9
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 10n:
      x10
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 11n:
      x11
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 12n:
      x12
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 13n:
      x13
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 14n:
      x14
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 15n:
      x15
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} _:
      T.W{0, 0}

# Lane n (0 <= n < 128) of a block.
def lane(+b: A.Block, +n: Nat) -> T.Lane:
  at(row_at(b, Nat.div(n, 16n)), Nat.mod(n, 16n))

# ---------------------------------------------------------------- indexing (RFC 9106 section 3.4)

def hi(x: T.Lane) -> U32:
  match x:
    case T.W{l, h}:
      h

def small(+x: Nat) -> T.Lane:
  T.W{U32.from_nat(x), 0}

# Z = (r, l, s, m', t, y, i), zero-padded to a block.
def input_of(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  A.B{T.V{small(r), small(l), small(s), small(mm), small(t), small(2n), small(ctr), T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}, T.V{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}}

# (r is inspected first, so the proofs keep an input block with a symbolic
# pass folded instead of compressing it symbolically.)
def input_block(r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  match r:
    case 0n:
      input_of(0n, l, s, mm, t, ctr)
    case 1n+x:
      input_of(1n+x, l, s, mm, t, ctr)

# The address block of counter ctr: G(0, G(0, Z)).
def addresses(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> A.Block:
  G.compress(G.zero(), G.compress(G.zero(), input_block(r, l, s, mm, t, ctr)))

# The address block for position idx: a new one at the segment's first
# position and at every multiple of 128 (data-independent segments only).
def regen(need: Bool, addr: A.Block, +r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +idx: Nat) -> A.Block:
  match need:
    case True{}:
      addresses(r, l, s, mm, t, Nat.add(Nat.div(idx, 128n), 1n))
    case False{}:
      addr

# |W|, the number of blocks the reference may be drawn from.
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

# |W| - 1 - (|W| * (J1^2 / 2^32)) / 2^32
def rel(+w: Nat, +j1: U32) -> Nat:
  +x = X.hi(X.mul32(j1, j1))
  Nat.sub(Nat.sub(w, 1n), U32.to_nat(X.hi(X.mul32(U32.from_nat(w), x))))

def start_last(+s: Nat, +sl: Nat, last: Bool) -> Nat:
  match last:
    case True{}:
      0n
    case False{}:
      Nat.mul(Nat.add(s, 1n), sl)

# The first block of the reference area: 0 in the first pass, else the start
# of the next segment (wrapping).
def start(r0: Bool, +s: Nat, +sl: Nat) -> Nat:
  match r0:
    case True{}:
      0n
    case False{}:
      start_last(s, sl, Nat.is_eq(s, 3n))

def ref_lane(forced: Bool, +l: Nat, +j2: U32, +p: Nat) -> Nat:
  match forced:
    case True{}:
      l
    case False{}:
      Nat.mod(U32.to_nat(j2), p)

def prev_index(+l: Nat, +q: Nat, +j: Nat, first: Bool) -> Nat:
  match first:
    case True{}:
      Nat.add(Nat.mul(l, q), Nat.sub(q, 1n))
    case False{}:
      Nat.sub(Nat.add(Nat.mul(l, q), j), 1n)

def pick(indep: Bool, +addr: A.Block, +idx: Nat, +prev: A.Block) -> T.Lane:
  match indep:
    case True{}:
      lane(addr, Nat.mod(idx, 128n))
    case False{}:
      lane(prev, 0n)

# ---------------------------------------------------------------- filling (RFC 9106 section 3.2, steps 5-6)

def store_xor(+cur: Nat, +prev: A.Block, +refb: A.Block, pair: Array<U32> & A.Block) -> Array<U32>:
  (a, old) = pair
  M.set(cur, G.compress_xor(prev, refb, old), a)

# B[l][j] = G(B[l][j-1], B[l'][z']), XORed into the old block after the first pass.
def store(r0: Bool, +cur: Nat, +prev: A.Block, +refb: A.Block, a: Array<U32>) -> Array<U32>:
  match r0:
    case True{}:
      M.set(cur, G.compress(prev, refb), a)
    case False{}:
      store_xor(cur, prev, refb, M.get(cur, a))

def with_ref(r0: Bool, +cur: Nat, +prev: A.Block, pair: Array<U32> & A.Block) -> Array<U32>:
  (a, +refb) = pair
  store(r0, cur, prev, refb, a)

# One block: pair holds the memory and the previous block.
def step(+r: Nat, +l: Nat, +s: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +cur: Nat, +indep: Bool, +addr: A.Block, pair: Array<U32> & A.Block) -> Array<U32>:
  (a, +prev) = pair
  +r0 = Nat.is_eq(r, 0n)
  +pr = pick(indep, addr, idx, prev)
  +rl = ref_lane(Bool.and(r0, Nat.is_eq(s, 0n)), l, hi(pr), p)
  +w = area(area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l))
  +ri = Nat.mod(Nat.add(start(r0, s, sl), rel(w, G.lo(pr))), q)
  with_ref(r0, cur, prev, M.get(Nat.add(Nat.mul(rl, q), ri), a))

# Positions idx .. idx + n - 1 of segment (r, s) of lane l.
def seg_go(n: Nat, +idx: Nat, first: Bool, addr: A.Block, a: Array<U32>, +r: Nat, +l: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +indep: Bool) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+rest:
      +addr2 = regen(Bool.and(indep, Bool.or(first, Nat.is_eq(Nat.mod(idx, 128n), 0n))), addr, r, l, s, mm, t, idx)
      +j = Nat.add(Nat.mul(s, sl), idx)
      +cur = Nat.add(Nat.mul(l, q), j)
      seg_go(rest, Nat.add(idx, 1n), False{}, addr2, step(r, l, s, idx, p, q, sl, cur, indep, addr2, M.get(prev_index(l, q, j, Nat.is_eq(j, 0n)), a)), r, l, s, p, q, sl, mm, t, indep)

def start_index(first: Bool) -> Nat:
  match first:
    case True{}:
      2n
    case False{}:
      0n

# Segment s of lane l in pass r; data-independent addressing in the first two
# slices of the first pass. The first two blocks of each lane are already set.
def segment(+r: Nat, +s: Nat, +l: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, a: Array<U32>) -> Array<U32>:
  +r0 = Nat.is_eq(r, 0n)
  +st = start_index(Bool.and(r0, Nat.is_eq(s, 0n)))
  seg_go(Nat.sub(sl, st), st, True{}, G.zero(), a, r, l, s, p, q, sl, mm, t, Bool.and(r0, Nat.is_lt(s, 2n)))

def lanes_go(n: Nat, +l: Nat, +r: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+rest:
      lanes_go(rest, Nat.add(l, 1n), r, s, p, q, sl, mm, t, segment(r, s, l, p, q, sl, mm, t, a))

def slices_go(n: Nat, +s: Nat, +r: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+rest:
      slices_go(rest, Nat.add(s, 1n), r, p, q, sl, mm, t, lanes_go(p, 0n, r, s, p, q, sl, mm, t, a))

def passes_go(n: Nat, +r: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+rest:
      passes_go(rest, Nat.add(r, 1n), p, q, sl, mm, t, slices_go(4n, 0n, r, p, q, sl, mm, t, a))

# B[l][0] = H'^1024(H0 || LE32(0) || LE32(l)), B[l][1] = H'^1024(H0 || LE32(1) || LE32(l)).
def init_go(n: Nat, +l: Nat, +q: Nat, +hh: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+rest:
      +b0 = block_of(hprime(1024n, cat(hh, cat(le32(0n), le32(l)))))
      +b1 = block_of(hprime(1024n, cat(hh, cat(le32(1n), le32(l)))))
      init_go(rest, Nat.add(l, 1n), q, hh, M.set(Nat.add(Nat.mul(l, q), 1n), b1, M.set(Nat.mul(l, q), b0, a)))

# C = B[0][q-1] XOR .. XOR B[p-1][q-1]: pair holds the memory and B[l][q-1],
# n more lanes follow.
def final_go(n: Nat, +l: Nat, +q: Nat, c: A.Block, pair: Array<U32> & A.Block) -> A.Block:
  match n pair:
    case 0n Tuple{a, b}:
      G.xor(c, b)
    case 1n+rest Tuple{a, b}:
      final_go(rest, Nat.add(l, 1n), q, G.xor(c, b), M.get(Nat.add(Nat.mul(Nat.add(l, 1n), q), Nat.sub(q, 1n)), a))

# ---------------------------------------------------------------- Argon2id

# RFC 9106 section 3.1 ranges: 1 <= p <= 2^24 - 1, 4 <= T <= 2^32 - 1,
# 8p <= m <= 2^32 - 1, 1 <= t <= 2^32 - 1, 8 <= |S| <= 2^32 - 1 and |P|,
# |K|, |X| <= 2^32 - 1.
def valid(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Bool:
  Bool.and(Bool.and(Bool.and(Nat.is_le(1n, p), Nat.is_le(p, 16777215n)), Bool.and(Nat.is_le(4n, tl), Nat.is_le(tl, 4294967295n))),
    Bool.and(Bool.and(Bool.and(Nat.is_le(Nat.mul(8n, p), m), Nat.is_le(m, 4294967295n)), Bool.and(Nat.is_le(1n, t), Nat.is_le(t, 4294967295n))),
      Bool.and(Bool.and(Nat.is_le(8n, len(salt)), Nat.is_le(len(salt), 4294967295n)), Bool.and(Nat.is_le(len(pw), 4294967295n), Bool.and(Nat.is_le(len(key), 4294967295n), Nat.is_le(len(ad), 4294967295n))))))

# m' = 4p floor(m / 4p), the number of blocks.
def blocks(+m: Nat, +p: Nat) -> Nat:
  Nat.mul(Nat.mul(4n, p), Nat.div(m, Nat.mul(4n, p)))

# This implementation's limit: the memory of m' blocks is an array of at most
# 2^31 words, so m' <= 2^23 (8 GiB), the RFC allowing up to 2^32 - 1 KiB.
def fits(+m: Nat, +p: Nat) -> Bool:
  Nat.is_le(M.levels(blocks(m, p)), 23n)

# The tag for valid parameters.
def run(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> List<&2, U32>:
  +mm = blocks(m, p)
  +q = Nat.div(mm, p)
  +sl = Nat.div(q, 4n)
  +k = M.levels(mm)
  +hh = h0(p, tl, m, t, pw, salt, key, ad)
  a = passes_go(t, 0n, p, q, sl, mm, t, init_go(p, 0n, q, hh, M.new(k)))
  hprime(tl, block_bytes(final_go(Nat.sub(p, 1n), 0n, q, G.zero(), M.get(Nat.sub(q, 1n), a))))

def checked(ok: Bool, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{run(pw, salt, key, ad, t, m, p, tl)}
    case False{}:
      None{}

# Argon2id(P, S, K, X; t passes, m KiB, p lanes, T tag bytes): the T-byte tag,
# or None when a parameter is out of the RFC 9106 ranges or the memory does
# not fit (fits).
def argon2id(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> Maybe<&2, List<&2, U32>>:
  checked(Bool.and(valid(pw, salt, key, ad, t, m, p, tl), fits(m, p)), pw, salt, key, ad, t, m, p, tl)
